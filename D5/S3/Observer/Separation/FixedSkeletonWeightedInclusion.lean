/- GID: D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/FixedSkeletonWeightedInclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: nonnested common-suffix replay
   digest: Suffix replay across nonnested cuts. -/

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

namespace D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion

/-- Assignments to the two separately labelled endpoint subsets. -/
def Values {I : Type*} (X Y : I → Type*) (l r : I → Prop) :=
  (∀ i : {i // l i}, X i.val) × (∀ i : {i // r i}, Y i.val)

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

open Classical in
/-- Actual row-image covering and packing have real extrema against all real feasible vectors.
The two extrema are separate; this statement does not identify their objective values. -/
theorem row_image_real_extrema {X Y Z : Type*} [Fintype X] [Fintype Z]
    (φ : X → Y → Z) (hφ : ∀ z, ∃ x y, φ x y = z) :
    (∃ lam : X → ℝ,
      (∀ x, 0 ≤ lam x ∧ lam x ≤ 1) ∧
      (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then lam x else 0) ∧
      ∀ μ : X → ℝ, (∀ x, 0 ≤ μ x) →
        (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then μ x else 0) →
        (∑ x, lam x) ≤ ∑ x, μ x) ∧
    (∃ w : Z → ℝ,
      (∀ z, 0 ≤ w z ∧ w z ≤ 1) ∧
      (∀ x, (∑ z, if (∃ y, φ x y = z) then w z else 0) ≤ 1) ∧
      ∀ v : Z → ℝ, (∀ z, 0 ≤ v z) →
        (∀ x, (∑ z, if (∃ y, φ x y = z) then v z else 0) ≤ 1) →
        (∑ z, v z) ≤ ∑ z, w z) := by
  constructor
  · classical
    let A : X → Z → Prop := fun x z => ∃ y, φ x y = z
    let K : Set (X → ℝ) := {lam | (∀ x, 0 ≤ lam x ∧ lam x ≤ 1) ∧
      ∀ z, 1 ≤ ∑ x, if A x z then lam x else 0}
    have hc : IsClosed K := by
      have heq : K = (⋂ x, {lam : X → ℝ | 0 ≤ lam x ∧ lam x ≤ 1}) ∩
          (⋂ z, {lam : X → ℝ | 1 ≤ ∑ x, if A x z then lam x else 0}) := by
        ext lam
        simp only [K, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      rw [heq]
      apply IsClosed.inter
      · apply isClosed_iInter
        intro x
        exact (isClosed_le continuous_const (continuous_apply x)).inter
          (isClosed_le (continuous_apply x) continuous_const)
      · apply isClosed_iInter
        intro z
        apply isClosed_le continuous_const
        apply continuous_finsetSum
        intro x hx
        by_cases h : A x z <;> simp only [h, if_true, if_false]
        · exact continuous_apply x
        · exact continuous_const
    have hk : IsCompact K := isCompact_Icc.of_isClosed_subset hc (by
      intro lam hlam
      exact ⟨fun x => (hlam.1 x).1, fun x => (hlam.1 x).2⟩)
    have hn : K.Nonempty := by
      refine ⟨fun _ => 1, (fun x => ⟨zero_le_one, le_rfl⟩), ?_⟩
      intro z
      obtain ⟨x,y,hxy⟩ := hφ z
      have ha : A x z := ⟨y,hxy⟩
      calc
        (1 : ℝ) = (if A x z then 1 else 0) := by simp [ha]
        _ ≤ ∑ u : X, if A u z then (1 : ℝ) else 0 :=
          by
            simpa using (Finset.single_le_sum (s := Finset.univ)
              (f := fun u : X => if A u z then (1 : ℝ) else 0)
              (fun u _ => by split_ifs <;> positivity) (Finset.mem_univ x))
    obtain ⟨lam,hlam,hmin⟩ := hk.exists_isMinOn hn
      (show Continuous (fun lam : X → ℝ => ∑ x, lam x) by fun_prop).continuousOn
    refine ⟨lam,hlam.1,hlam.2,?_⟩
    intro μ hμ hcover
    let ν : X → ℝ := fun x => min (μ x) 1
    have hν : ν ∈ K := by
      refine ⟨fun x => ⟨le_min (hμ x) zero_le_one, min_le_right _ _⟩,?_⟩
      intro z
      by_cases hlarge : ∃ x, A x z ∧ 1 ≤ μ x
      · obtain ⟨x,ha,hx⟩ := hlarge
        calc
          (1 : ℝ) = (if A x z then ν x else 0) := by simp [ha,ν,min_eq_right hx]
          _ ≤ ∑ u : X, if A u z then ν u else 0 :=
            by
              simpa using (Finset.single_le_sum (s := Finset.univ)
                (f := fun u : X => if A u z then ν u else 0)
                (fun u _ => by
                  split_ifs
                  · exact le_min (hμ u) zero_le_one
                  · exact le_rfl) (Finset.mem_univ x))
      · have he : (∑ x, if A x z then ν x else 0) =
            ∑ x, if A x z then μ x else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases ha : A x z
          · have hlt : μ x < 1 := lt_of_not_ge (fun h => hlarge ⟨x,ha,h⟩)
            simp [ha,ν,min_eq_left hlt.le]
          · simp [ha]
        rw [he]
        exact hcover z
    exact (hmin hν).trans (Finset.sum_le_sum (fun x _ => min_le_left (μ x) 1))
  · classical
    let A : X → Z → Prop := fun x z => ∃ y, φ x y = z
    let K : Set (Z → ℝ) := {w | (∀ z, 0 ≤ w z) ∧
      ∀ x, (∑ z, if A x z then w z else 0) ≤ 1}
    have hc : IsClosed K := by
      have heq : K = (⋂ z, {w : Z → ℝ | 0 ≤ w z}) ∩
          (⋂ x, {w : Z → ℝ | (∑ z, if A x z then w z else 0) ≤ 1}) := by
        ext w
        simp only [K, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      rw [heq]
      apply IsClosed.inter
      · exact isClosed_iInter (fun z => isClosed_le continuous_const (continuous_apply z))
      · apply isClosed_iInter
        intro x
        apply isClosed_le _ continuous_const
        apply continuous_finsetSum
        intro z hz
        by_cases h : A x z <;> simp only [h, if_true, if_false]
        · exact continuous_apply z
        · exact continuous_const
    have hbound : ∀ w ∈ K, ∀ z, w z ≤ 1 := by
      intro w hw z
      obtain ⟨x,y,hxy⟩ := hφ z
      have ha : A x z := ⟨y,hxy⟩
      calc
        w z = (if A x z then w z else 0) := by simp [ha]
        _ ≤ ∑ u : Z, if A x u then w u else 0 :=
          by
            simpa using (Finset.single_le_sum (s := Finset.univ)
              (f := fun u : Z => if A x u then w u else 0)
              (fun u _ => by
              split_ifs
              · exact hw.1 u
              · exact le_rfl) (Finset.mem_univ z))
        _ ≤ 1 := hw.2 x
    have hk : IsCompact K := isCompact_Icc.of_isClosed_subset hc (by
      intro w hw
      exact ⟨hw.1, hbound w hw⟩)
    have hn : K.Nonempty := ⟨fun _ => 0, (fun _ => le_rfl), by simp⟩
    obtain ⟨w,hw,hmax⟩ := hk.exists_isMaxOn hn
      (show Continuous (fun w : Z → ℝ => ∑ z, w z) by fun_prop).continuousOn
    exact ⟨w,(fun z => ⟨hw.1 z,hbound w hw z⟩),hw.2,
      fun v hv hc => hmax ⟨hv,hc⟩⟩

open Classical in
/-- Actual row-image incidence admits equal real cover and packing optima.
Both optimizing comparisons range over every real feasible competitor. -/
theorem row_image_real_duality {X Y Z : Type*} [Fintype X] [Fintype Z] [Nonempty Z]
    (φ : X → Y → Z) (hφ : ∀ z, ∃ x y, φ x y = z) :
    ∃ lam : X → ℝ, ∃ w : Z → ℝ,
      (∀ x, 0 ≤ lam x) ∧
      (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then lam x else 0) ∧
      (∀ z, 0 ≤ w z) ∧
      (∀ x, (∑ z, if (∃ y, φ x y = z) then w z else 0) ≤ 1) ∧
      (∑ x, lam x) = (∑ z, w z) ∧
      (∀ μ : X → ℝ, (∀ x, 0 ≤ μ x) →
        (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then μ x else 0) →
        (∑ x, lam x) ≤ ∑ x, μ x) ∧
      (∀ v : Z → ℝ, (∀ z, 0 ≤ v z) →
        (∀ x, (∑ z, if (∃ y, φ x y = z) then v z else 0) ≤ 1) →
        (∑ z, v z) ≤ ∑ z, w z) := by
  classical
  obtain ⟨lam,hlam,hcover,hmin⟩ := (row_image_real_extrema φ hφ).1
  let A : X → Z → Prop := fun x z => ∃ y, φ x y = z
  let τ : ℝ := ∑ x, lam x
  have hτ : 0 < τ := by
    have hz := hcover (Classical.arbitrary Z)
    have hs : (∑ x, if A x (Classical.arbitrary Z) then lam x else 0) ≤ τ := by
      apply Finset.sum_le_sum
      intro x hx
      split_ifs
      · exact le_rfl
      · exact (hlam x).1
    linarith
  let γ := τ⁻¹
  have hγ : 0 < γ := inv_pos.mpr hτ
  let L : (X → ℝ) →ₗ[ℝ] (Z → ℝ) := {
    toFun := fun p z => ∑ x, if A x z then p x else 0
    map_add' := by
      intro p q
      funext z
      change (∑ x, if A x z then p x + q x else 0) =
        (∑ x, if A x z then p x else 0) + ∑ x, if A x z then q x else 0
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp
    map_smul' := by
      intro c p
      funext z
      change (∑ x, if A x z then c * p x else 0) =
        c * ∑ x, if A x z then p x else 0
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp }
  let K := L '' stdSimplex ℝ X
  let U : Set (Z → ℝ) := {v | ∀ z, γ < v z}
  have hUeq : U = ⋂ z, {v : Z → ℝ | γ < v z} := by
    ext v; simp [U]
  have hUconv : Convex ℝ U := by
    rw [hUeq]
    apply convex_iInter
    intro z
    exact (show Convex ℝ (Set.Ioi γ) from convex_Ioi γ).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Z => ℝ) z)
  have hUopen : IsOpen U := by
    rw [hUeq]
    exact isOpen_iInter_of_finite (fun z => isOpen_lt continuous_const (continuous_apply z))
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ X).linear_image L
  have hdisj : Disjoint U K := by
    apply Set.disjoint_left.mpr
    intro k hkU hkK
    obtain ⟨p,hp,rfl⟩ := hkK
    let V := Finset.univ.image (L p)
    have hV : V.Nonempty := ⟨L p (Classical.arbitrary Z), Finset.mem_image.mpr
      ⟨Classical.arbitrary Z,Finset.mem_univ _,rfl⟩⟩
    let β := V.min' hV
    have hγβ : γ < β := by
      obtain ⟨z,hz,hval⟩ := Finset.mem_image.mp (Finset.min'_mem V hV)
      change γ < V.min' hV
      rw [← hval]
      exact hkU z
    have hβ : 0 < β := hγ.trans hγβ
    have hβle : ∀ z, β ≤ L p z := fun z => Finset.min'_le V _
      (Finset.mem_image.mpr ⟨z,Finset.mem_univ z,rfl⟩)
    have hμcover : ∀ z, 1 ≤ ∑ x, if A x z then p x / β else 0 := by
      intro z
      have he : (∑ x, if A x z then p x / β else 0) = L p z / β := by
        dsimp [L]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x hx
        split_ifs <;> simp
      rw [he]
      exact (le_div_iff₀ hβ).mpr (by simpa using hβle z)
    have hm := hmin (fun x => p x / β) (fun x => div_nonneg (hp.1 x) hβ.le) hμcover
    have hsum : (∑ x, p x / β) = β⁻¹ := by rw [← Finset.sum_div, hp.2, one_div]
    have hlt : β⁻¹ < τ := by
      have hh := (inv_lt_inv₀ hβ hγ).mpr hγβ
      simpa [γ] using hh
    rw [hsum] at hm
    exact (not_lt_of_ge hm hlt)
  obtain ⟨f,u,hfu,hfk⟩ := geometric_hahn_banach_open hUconv hUopen hKconv hdisj
  let a : Z → ℝ := fun z => - f (Pi.single z 1)
  have frep : ∀ v : Z → ℝ, f v = ∑ z, f (Pi.single z 1) * v z := by
    intro v
    have hv : v = ∑ z, v z • (Pi.single z 1) := by
      funext z
      simp [Finset.sum_apply,Pi.single_apply]
    calc
      f v = f (∑ z, v z • Pi.single z 1) := congrArg f hv
      _ = ∑ z, f (Pi.single z 1) * v z := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro z hz
        simp [map_smul,smul_eq_mul,mul_comm]
  have ha : ∀ z, 0 ≤ a z := by
    intro z
    change 0 ≤ - f (Pi.single z 1)
    apply neg_nonneg.mpr
    by_contra hn
    have hf : 0 < f (Pi.single z 1) := lt_of_not_ge hn
    let v₀ : Z → ℝ := fun _ => γ + 1
    have h₀ : v₀ ∈ U := by intro j; dsimp [v₀]; linarith
    have hbase := hfu v₀ h₀
    let t := (u - f v₀ + 1) / f (Pi.single z 1)
    have ht : 0 ≤ t := div_nonneg (by linarith) hf.le
    have hv : v₀ + t • Pi.single z 1 ∈ U := by
      intro j
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      by_cases hj : j = z
      · subst j; simp [v₀] <;> linarith
      · simp [v₀,Pi.single_eq_of_ne hj]
    have hsep := hfu _ hv
    have he : f (v₀ + t • Pi.single z 1) = u + 1 := by
      rw [map_add,map_smul]
      change f v₀ + ((u - f v₀ + 1) / f (Pi.single z 1)) * f (Pi.single z 1) = u + 1
      field_simp <;> ring
    linarith
  let S := ∑ z, a z
  have hS : 0 < S := by
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun z _ => ha z)
    by_contra hn
    have hzero : S = 0 := le_antisymm (le_of_not_gt hn) hS0
    have haz : ∀ z, a z = 0 := fun z =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => ha z)).mp hzero z (Finset.mem_univ z)
    have hfzero : ∀ v : Z → ℝ, f v = 0 := by
      intro v
      rw [frep]
      have he : ∀ z, f (Pi.single z 1) = 0 := fun z => neg_eq_zero.mp (haz z)
      simp [he]
    obtain ⟨x,y,hxy⟩ := hφ (Classical.arbitrary Z)
    have hleft := hfu (fun _ => γ + 1) (by intro z; linarith)
    have hright := hfk (L (Pi.single x 1))
      (Set.mem_image_of_mem L (single_mem_stdSimplex ℝ x))
    rw [hfzero] at hleft hright
    linarith
  have hb : ∀ k ∈ K, (∑ z, a z * k z) ≤ γ * S := by
    intro k hk
    by_contra hn
    have hg : γ * S < ∑ z, a z * k z := lt_of_not_ge hn
    let ε := ((∑ z, a z * k z) / S - γ) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      have hgt : γ < (∑ z, a z * k z) / S := (lt_div_iff₀ hS).mpr hg
      linarith
    have hv : (fun _ : Z => γ + ε) ∈ U := by intro z; linarith
    have hleft := hfu _ hv
    have hright := hfk k hk
    rw [frep] at hleft hright
    have hfconst : (∑ z, f (Pi.single z 1) * (γ + ε)) = -(S * (γ + ε)) := by
      rw [Finset.sum_mul]
      simp [a,Finset.sum_neg_distrib]
    have hfkneg : (∑ z, f (Pi.single z 1) * k z) = -(∑ z, a z * k z) := by
      dsimp [a]
      simp [Finset.sum_neg_distrib]
    rw [hfconst] at hleft
    rw [hfkneg] at hright
    have hεeq : S * ε = ((∑ z, a z * k z) - S * γ) / 2 := by
      dsimp [ε]; field_simp
    nlinarith
  let w : Z → ℝ := fun z => a z / (γ * S)
  have hw : ∀ z, 0 ≤ w z := fun z => div_nonneg (ha z) (mul_pos hγ hS).le
  have hload : ∀ x, (∑ z, if A x z then w z else 0) ≤ 1 := by
    intro x
    have hbcol := hb (L (Pi.single x 1)) (Set.mem_image_of_mem L (single_mem_stdSimplex ℝ x))
    have he : (∑ z, if A x z then w z else 0) =
        (∑ z, a z * L (Pi.single x 1) z) / (γ * S) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z hz
      have hL : L (Pi.single x 1) z = if A x z then 1 else 0 := by
        dsimp [L]
        rw [Finset.sum_eq_single x]
        · simp
        · intro b hb hbx
          simp [Pi.single_eq_of_ne hbx]
        · simp
      rw [hL]
      by_cases har : A x z <;> simp [har,w]
    rw [he]
    exact (div_le_one (mul_pos hγ hS)).mpr hbcol
  have heq : (∑ z, w z) = τ := by
    dsimp [w]
    rw [← Finset.sum_div]
    change S / (γ * S) = τ
    dsimp [γ]
    field_simp
  have hweak : ∀ v : Z → ℝ, (∀ z, 0 ≤ v z) →
      (∀ x, (∑ z, if A x z then v z else 0) ≤ 1) → (∑ z, v z) ≤ τ := by
    intro v hv hvl
    calc
      (∑ z, v z) = ∑ z, v z * 1 := by simp
      _ ≤ ∑ z, v z * (∑ x, if A x z then lam x else 0) := by
        apply Finset.sum_le_sum
        intro z hz
        exact mul_le_mul_of_nonneg_left (hcover z) (hv z)
      _ = ∑ x, lam x * (∑ z, if A x z then v z else 0) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro z hz
        split_ifs <;> ring
      _ ≤ ∑ x, lam x * 1 := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hvl x) (hlam x).1
      _ = τ := by simp [τ]
  refine ⟨lam,w,(fun x => (hlam x).1),hcover,hw,hload,heq.symm,hmin,?_⟩
  intro v hv hvl
  rw [heq]
  exact hweak v hv hvl

open Classical in
/-- Every real direction annihilated by the original active normals at an extreme point vanishes. -/
theorem active_constraint_kernel_zero {I J : Type*} [Fintype I] [Fintype J]
    (a : J → (I → ℝ) →ₗ[ℝ] ℝ) (b : J → ℝ) (v : I → ℝ)
    (hv : v ∈ Set.extremePoints ℝ {u : I → ℝ | ∀ j, a j u ≤ b j})
    (d : I → ℝ) (hd : ∀ j, a j v = b j → a j d = 0) : d = 0 := by
  classical
  let δ : J → ℝ := fun j => if a j v = b j then 1 else
    (b j - a j v) / (|a j d| + 1)
  have hδ : ∀ j, 0 < δ j := by
    intro j
    dsimp [δ]
    split_ifs with h
    · exact zero_lt_one
    · exact div_pos (sub_pos.mpr (lt_of_le_of_ne (hv.1 j) h)) (by positivity)
  let S : Finset ℝ := insert 1 (Finset.univ.image δ)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  let ε := S.min' hS
  have hε : 0 < ε := by
    have ht : ε ∈ S := Finset.min'_mem S hS
    rcases Finset.mem_insert.mp ht with ht | ht
    · rw [ht]; exact zero_lt_one
    · obtain ⟨j,_,hj⟩ := Finset.mem_image.mp ht
      rw [← hj]; exact hδ j
  have hεle : ∀ j, ε ≤ δ j := fun j => Finset.min'_le S _
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  have hfeas : ∀ t : ℝ, |t| ≤ ε → ∀ j, a j (v + t • d) ≤ b j := by
    intro t ht j
    rw [map_add,map_smul]
    change a j v + t * a j d ≤ b j
    by_cases hj : a j v = b j
    · rw [hd j hj, mul_zero, add_zero, hj]
    · have hs : ε * (|a j d| + 1) ≤ b j - a j v := by
        apply (le_div_iff₀ (by positivity : 0 < |a j d| + 1)).mp
        simpa [δ,hj] using hεle j
      have hab : |t * a j d| ≤ ε * |a j d| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
      have hu := le_abs_self (t * a j d)
      have ha := abs_nonneg (a j d)
      nlinarith
  have hp := hfeas ε (by rw [abs_of_pos hε])
  have hm := hfeas (-ε) (by rw [abs_neg,abs_of_pos hε])
  have hmid : v ∈ openSegment ℝ (v + ε • d) (v + (-ε) • d) := by
    refine ⟨(1/2 : ℝ),(1/2 : ℝ),by norm_num,by norm_num,by norm_num,?_⟩
    ext i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have he := hv.2 hp hm hmid
  apply funext
  intro i
  have hi := congrFun he i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hi
  change d i = 0
  have hz : ε * d i = 0 := by linarith
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hε)



/-- An extreme point of finite original rational inequalities has rational coordinates. -/
theorem rational_extreme_point {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix J I ℚ) (b : J → ℚ) (v : I → ℝ)
    (hv : v ∈ Set.extremePoints ℝ
      {u : I → ℝ | ∀ j, (∑ i, (A j i : ℝ) * u i) ≤ (b j : ℝ)}) :
    ∃ q : I → ℚ, (fun i => (q i : ℝ)) = v := by
  classical
  let a : J → (I → ℝ) →ₗ[ℝ] ℝ := fun j =>
    (LinearMap.proj j).comp (Matrix.mulVecLin (fun j i => (A j i : ℝ)))
  let K := {j : J // a j v = (b j : ℝ)}
  let M : Matrix K I ℚ := fun j i => A j.val i
  let N : Matrix K I ℝ := fun j i => (M j i : ℝ)
  let c : K → ℚ := fun j => b j.val
  have hN : ∀ d : I → ℝ, N.mulVec d = 0 → d = 0 := by
    intro d hd
    apply active_constraint_kernel_zero a (fun j => (b j : ℝ)) v hv d
    intro j hj
    have h := congrFun hd (⟨j,hj⟩ : K)
    change (∑ i, (A j i : ℝ) * d i) = 0
    simpa [N,M,Matrix.mulVec,dotProduct] using h
  have hM : ∀ d : I → ℚ, M.mulVec d = 0 → d = 0 := by
    intro d hd
    have hr : N.mulVec (fun i => (d i : ℝ)) = 0 := by
      funext j
      have h := congrArg (fun t : ℚ => (t : ℝ)) (congrFun hd j)
      simpa [N,Matrix.mulVec,dotProduct] using h
    have hh := hN _ hr
    funext i
    have hi := congrFun hh i
    change (d i : ℝ) = 0 at hi
    change d i = 0
    exact_mod_cast hi
  have hG : Function.Injective (N.transpose * N).mulVec := by
    change Function.Injective (N.transpose * N).mulVecLin
    apply LinearMap.ker_eq_bot.mp
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact LinearMap.ker_eq_bot'.mpr (by simpa only [Matrix.mulVecLin_apply] using hN)
  have hB : Function.Injective (M.transpose * M).mulVec := by
    change Function.Injective (M.transpose * M).mulVecLin
    apply LinearMap.ker_eq_bot.mp
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact LinearMap.ker_eq_bot'.mpr (by simpa only [Matrix.mulVecLin_apply] using hM)
  obtain ⟨q,hq⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    (Matrix.mulVec_injective_iff_isUnit.mp hB)) (M.transpose.mulVec c)
  refine ⟨q,hG ?_⟩
  have hvN : N.mulVec v = fun j => (c j : ℝ) := by
    funext j
    exact j.property
  have hqR : (N.transpose * N).mulVec (fun i => (q i : ℝ)) =
      N.transpose.mulVec (fun j => (c j : ℝ)) := by
    funext i
    have hh := congrArg (fun t : ℚ => (t : ℝ)) (congrFun hq i)
    change (∑ k, (∑ j, (M j i : ℝ) * (M j k : ℝ)) * (q k : ℝ)) =
      ∑ j, (M j i : ℝ) * (c j : ℝ)
    simpa [Matrix.mulVec,Matrix.mul_apply,Matrix.transpose_apply,dotProduct] using hh
  rw [hqR, ← Matrix.mulVec_mulVec, hvN]

private theorem rational_point_on_compact_face {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix J I ℚ) (b : J → ℚ) (F : Set (I → ℝ))
    (hcompact : IsCompact F) (hne : F.Nonempty)
    (hexposed : IsExposed ℝ
      {u : I → ℝ | ∀ j, (∑ i, (A j i : ℝ) * u i) ≤ (b j : ℝ)} F) :
    ∃ q : I → ℚ, (fun i => (q i : ℝ)) ∈ F := by
  obtain ⟨v,hv⟩ := hcompact.extremePoints_nonempty hne
  obtain ⟨q,hq⟩ := rational_extreme_point A b v
    (hexposed.isExtreme.extremePoints_subset_extremePoints hv)
  exact ⟨q, hq.symm ▸ hv.1⟩

open Classical in
/-- Equal rational actual row-image certificates attain both optima against all real competitors. -/
theorem row_image_rational_duality {X Y Z : Type*} [Fintype X] [Fintype Z] [Nonempty Z]
    (φ : X → Y → Z) (hφ : ∀ z, ∃ x y, φ x y = z) :
    ∃ lam : X → ℚ, ∃ w : Z → ℚ,
      (∀ x, 0 ≤ lam x) ∧
      (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then lam x else 0) ∧
      (∀ z, 0 ≤ w z) ∧
      (∀ x, (∑ z, if (∃ y, φ x y = z) then w z else 0) ≤ 1) ∧
      (∑ x, lam x) = (∑ z, w z) ∧
      (∀ μ : X → ℝ, (∀ x, 0 ≤ μ x) →
        (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then μ x else 0) →
        (∑ x, (lam x : ℝ)) ≤ ∑ x, μ x) ∧
      (∀ v : Z → ℝ, (∀ z, 0 ≤ v z) →
        (∀ x, (∑ z, if (∃ y, φ x y = z) then v z else 0) ≤ 1) →
        (∑ z, v z) ≤ ∑ z, (w z : ℝ)) := by
  classical
  obtain ⟨lam,w,hl,hcover,hw,hpack,heq,hmin,hmax⟩ := row_image_real_duality φ hφ
  let AP : Matrix (X ⊕ Z) X ℚ := fun j i => match j with
    | .inl x => if i = x then -1 else 0
    | .inr z => if (∃ y, φ i y = z) then -1 else 0
  let bP : X ⊕ Z → ℚ := fun j => match j with
    | .inl _ => 0
    | .inr _ => -1
  let AD : Matrix (Z ⊕ X) Z ℚ := fun j i => match j with
    | .inl z => if i = z then -1 else 0
    | .inr x => if (∃ y, φ x y = i) then 1 else 0
  let bD : Z ⊕ X → ℚ := fun j => match j with
    | .inl _ => 0
    | .inr _ => 1
  let P : Set (X → ℝ) := {u | ∀ j, (∑ i, (AP j i : ℝ) * u i) ≤ (bP j : ℝ)}
  let D : Set (Z → ℝ) := {u | ∀ j, (∑ i, (AD j i : ℝ) * u i) ≤ (bD j : ℝ)}
  have ep : ∀ u : X → ℝ, u ∈ P ↔ (∀ x, 0 ≤ u x) ∧
      (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then u x else 0) := by
    intro u
    have row : ∀ z, (∑ i, (AP (.inr z) i : ℝ) * u i) =
        -(∑ i, if (∃ y, φ i y = z) then u i else 0) := by
      intro z
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : ∃ y, φ i y = z <;> simp [AP,h]
    have diag : ∀ x, (∑ i, (AP (.inl x) i : ℝ) * u i) = -u x := by
      intro x
      rw [Finset.sum_eq_single x]
      · simp [AP]
      · intro i hi hn; simp [AP,hn]
      · simp
    constructor
    · intro hu
      refine ⟨fun x => ?_, fun z => ?_⟩
      · have hh := hu (.inl x)
        simpa [bP,diag] using hh
      · have hh := hu (.inr z)
        rw [row] at hh
        simpa [bP] using hh
    · rintro ⟨hu,hc⟩ j
      cases j with
      | inl x => simpa [bP,diag] using hu x
      | inr z => rw [row]; simpa [bP] using hc z
  have ed : ∀ u : Z → ℝ, u ∈ D ↔ (∀ z, 0 ≤ u z) ∧
      (∀ x, (∑ z, if (∃ y, φ x y = z) then u z else 0) ≤ 1) := by
    intro u
    have row : ∀ x, (∑ i, (AD (.inr x) i : ℝ) * u i) =
        ∑ i, if (∃ y, φ x y = i) then u i else 0 := by
      intro x
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : ∃ y, φ x y = i <;> simp [AD,h]
    have diag : ∀ z, (∑ i, (AD (.inl z) i : ℝ) * u i) = -u z := by
      intro z
      rw [Finset.sum_eq_single z]
      · simp [AD]
      · intro i hi hn; simp [AD,hn]
      · simp
    constructor
    · intro hu
      refine ⟨fun z => ?_, fun x => ?_⟩
      · have hh := hu (.inl z)
        simpa [bD,diag] using hh
      · have hh := hu (.inr x)
        rw [row] at hh
        simpa [bD] using hh
    · rintro ⟨hu,hc⟩ j
      cases j with
      | inl z => simpa [bD,diag] using hu z
      | inr x => rw [row]; simpa [bD] using hc x
  have hPc : IsClosed P := by
    have hp : P = ⋂ j, {u : X → ℝ | (∑ i, (AP j i : ℝ) * u i) ≤ (bP j : ℝ)} := by
      ext u; simp [P]
    rw [hp]
    exact isClosed_iInter (fun j => isClosed_le (by fun_prop) continuous_const)
  have hDc : IsClosed D := by
    have hp : D = ⋂ j, {u : Z → ℝ | (∑ i, (AD j i : ℝ) * u i) ≤ (bD j : ℝ)} := by
      ext u; simp [D]
    rw [hp]
    exact isClosed_iInter (fun j => isClosed_le (by fun_prop) continuous_const)
  let FP : Set (X → ℝ) := {u | u ∈ P ∧ (∑ x, u x) = ∑ x, lam x}
  let FD : Set (Z → ℝ) := {u | u ∈ D ∧ (∑ z, u z) = ∑ z, w z}
  have hlam : lam ∈ P := (ep lam).mpr ⟨hl,hcover⟩
  have hwD : w ∈ D := (ed w).mpr ⟨hw,hpack⟩
  have hFPc : IsClosed FP := hPc.inter (isClosed_eq (by fun_prop) continuous_const)
  have hFDc : IsClosed FD := hDc.inter (isClosed_eq (by fun_prop) continuous_const)
  have hFPk : IsCompact FP := isCompact_Icc.of_isClosed_subset hFPc (by
    intro u hu
    have hn := ((ep u).mp hu.1).1
    refine ⟨hn,fun x => ?_⟩
    change u x ≤ ∑ x, lam x
    rw [← hu.2]
    exact Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ x))
  have hFDk : IsCompact FD := isCompact_Icc.of_isClosed_subset hFDc (by
    intro u hu
    obtain ⟨hn,hc⟩ := (ed u).mp hu.1
    refine ⟨hn,fun z => ?_⟩
    obtain ⟨x,y,hxy⟩ := hφ z
    have ha : ∃ y, φ x y = z := ⟨y,hxy⟩
    calc
      u z = (if (∃ y, φ x y = z) then u z else 0) := by simp [ha]
      _ ≤ ∑ t, if (∃ y, φ x y = t) then u t else 0 :=
        Finset.single_le_sum (f := fun t => if (∃ y, φ x y = t) then u t else 0)
          (fun t _ => by split_ifs; exact hn t; exact le_rfl) (Finset.mem_univ z)
      _ ≤ 1 := hc x)
  have hFPexp : IsExposed ℝ P FP := by
    intro _
    refine ⟨-(∑ x : X, ContinuousLinearMap.proj x), ?_⟩
    ext u
    constructor
    · rintro ⟨hu,he⟩
      refine ⟨hu,fun t ht => ?_⟩
      have hm := hmin t ((ep t).mp ht).1 ((ep t).mp ht).2
      simp only [neg_apply, sum_apply,
        ContinuousLinearMap.proj_apply]
      linarith
    · rintro ⟨hu,hm⟩
      have hh := hm lam hlam
      have hlower := hmin u ((ep u).mp hu).1 ((ep u).mp hu).2
      simp only [neg_apply, sum_apply,
        ContinuousLinearMap.proj_apply] at hh
      exact ⟨hu, by linarith⟩
  have hFDexp : IsExposed ℝ D FD := by
    intro _
    refine ⟨∑ z : Z, ContinuousLinearMap.proj z, ?_⟩
    ext u
    constructor
    · rintro ⟨hu,he⟩
      refine ⟨hu,fun t ht => ?_⟩
      have hm := hmax t ((ed t).mp ht).1 ((ed t).mp ht).2
      simp only [sum_apply, ContinuousLinearMap.proj_apply]
      linarith
    · rintro ⟨hu,hm⟩
      have hh := hm w hwD
      have hupper := hmax u ((ed u).mp hu).1 ((ed u).mp hu).2
      simp only [sum_apply, ContinuousLinearMap.proj_apply] at hh
      exact ⟨hu, by linarith⟩
  obtain ⟨q,hq⟩ := rational_point_on_compact_face AP bP FP hFPk ⟨lam,hlam,rfl⟩ hFPexp
  obtain ⟨r,hr⟩ := rational_point_on_compact_face AD bD FD hFDk ⟨w,hwD,rfl⟩ hFDexp
  have hpq := (ep (fun x => (q x : ℝ))).mp hq.1
  have hdr := (ed (fun z => (r z : ℝ))).mp hr.1
  refine ⟨q,r,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x; exact_mod_cast hpq.1 x
  · intro z
    have hc : ((∑ x, if (∃ y, φ x y = z) then q x else 0 : ℚ) : ℝ) =
        ∑ x, if (∃ y, φ x y = z) then (q x : ℝ) else 0 := by
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp
    have hh := hpq.2 z
    rw [← hc] at hh
    exact_mod_cast hh
  · intro z; exact_mod_cast hdr.1 z
  · intro x
    have hc : ((∑ z, if (∃ y, φ x y = z) then r z else 0 : ℚ) : ℝ) =
        ∑ z, if (∃ y, φ x y = z) then (r z : ℝ) else 0 := by
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro z hz
      split_ifs <;> simp
    have hh := hdr.2 x
    rw [← hc] at hh
    exact_mod_cast hh
  · have hh : (∑ x, (q x : ℝ)) = ∑ z, (r z : ℝ) := hq.2.trans (heq.trans hr.2.symm)
    exact_mod_cast hh
  · intro μ hn hc
    rw [hq.2]
    exact hmin μ hn hc
  · intro v hn hc
    rw [hr.2]
    exact hmax v hn hc


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
theorem fractional_relation_log_bound {C A R : Type*} [Fintype C] [Nonempty C]
    [Fintype A] [Fintype R] [DecidableEq A]
    {V : A → Type*} [∀ a, Fintype (V a)]
    (H : C → ∀ a, V a) (S : R → Finset A) (w : R → ℝ)
    (hw : ∀ r, 0 ≤ w r)
    (hcover : ∀ a, 1 ≤ ∑ r, if a ∈ S r then w r else 0) :
    Real.log (Nat.card (Set.range H)) ≤
      ∑ r, w r * Real.log (Nat.card
        (Set.range (coordinateTuple (fun a c => H c a) (S r)))) := by
  classical
  let T := Set.range H
  letI : Fintype T := Fintype.ofFinite T
  letI : Nonempty T := ⟨⟨H (Classical.arbitrary C),Set.mem_range_self _⟩⟩
  let p : T → ℝ := fun _ => (Fintype.card T : ℝ)⁻¹
  have hpos : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  have hp : (∀ t, 0 ≤ p t) ∧ ∑ t, p t = 1 := by
    refine ⟨fun _ => (inv_pos.mpr hpos).le,?_⟩
    simp only [p,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ (ne_of_gt hpos)
  let u : ∀ a, T → V a := fun a t => t.val a
  have hc := weighted_coordinate_entropy p hp u S w hw hcover
  have hf : coordinateEntropy p u Finset.univ = Real.log (Nat.card T) := by
    have hi : Function.Injective (coordinateTuple u Finset.univ) := by
      intro t t' he
      apply Subtype.ext
      funext a
      exact congrFun he ⟨a,Finset.mem_univ a⟩
    have he := (pushforward_entropy_eq_iff_injective_on_support p
      (coordinateTuple u Finset.univ) hp).2 hi.injOn
    have hu := (D5.S3.Entropy.EntropyEquality.entropy_eq_log_card_iff_uniform p hp).2 rfl
    simpa [coordinateEntropy,Nat.card_eq_fintype_card] using he.trans hu
  have hr : ∀ r, coordinateEntropy p u (S r) ≤ Real.log (Nat.card
      (Set.range (coordinateTuple (fun a c => H c a) (S r)))) := by
    intro r
    let rho := coordinateTuple u (S r)
    let Q := Set.range rho
    letI : Fintype Q := Fintype.ofFinite Q
    let lift : T → Q := fun t => ⟨rho t,Set.mem_range_self _⟩
    letI : Nonempty Q := ⟨lift (Classical.arbitrary T)⟩
    let inclusion : Q → (∀ a : {a // a ∈ S r}, V a.val) := Subtype.val
    have hq := pushforward_is_law p lift hp
    have he := (pushforward_entropy_eq_iff_injective_on_support
      (pushforward lift p) inclusion hq).2 (Subtype.val_injective.injOn)
    rw [pushforward_comp] at he
    have hbound := entropy_le_log_card (pushforward lift p) hq
    have ranges : Set.range rho =
        Set.range (coordinateTuple (fun a c => H c a) (S r)) := by
      ext v
      constructor
      · rintro ⟨t,ht⟩
        obtain ⟨c,hc⟩ := t.property
        refine ⟨c,?_⟩
        have h : coordinateTuple (fun a c => H c a) (S r) c = rho t := by
          funext a; exact congrFun hc a.val
        exact h.trans ht
      · rintro ⟨c,hc⟩
        exact ⟨⟨H c,Set.mem_range_self _⟩,hc⟩
    change shannonEntropy (pushforward rho p) ≤ _
    have hid : inclusion ∘ lift = rho := rfl
    rw [hid] at he
    rw [he]
    simpa [Q,ranges,Nat.card_eq_fintype_card] using hbound
  rw [hf] at hc
  exact hc.trans (Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (hr r) (hw r)))


local instance finiteValues {I : Type*} [Finite I] {X Y : I → Type*}
    [∀ i, Finite (X i)] [∀ i, Finite (Y i)] (l r : I → Prop) :
    Finite (Values X Y l r) := by
  unfold Values
  infer_instance

local instance nonemptyValues {I : Type*} {X Y : I → Type*}
    [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)] (l r : I → Prop) :
    Nonempty (Values X Y l r) := by
  unfold Values
  infer_instance

private theorem range_card_le_of_kernel {C A B : Type*}
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
private theorem actual_group_nonempty {I : Type*} {X Y : I → Type*}
    [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)]
    (designated B₁ B₂ P₁ P₂ : I → Prop)
    (c : Values X Y (fun i => designated i ∧ B₁ i ∧ ¬P₁ i)
      (fun i => designated i ∧ B₂ i ∧ ¬P₂ i)) :
    Nonempty {b : Values X Y B₁ B₂ // InGroup designated B₁ B₂ P₁ P₂ b c} := by
  classical
  let b : Values X Y B₁ B₂ :=
    (fun i => if h : designated i.val ∧ B₁ i.val ∧ ¬P₁ i.val then c.1 ⟨i.val,h⟩
       else Classical.arbitrary (X i.val),
     fun i => if h : designated i.val ∧ B₂ i.val ∧ ¬P₂ i.val then c.2 ⟨i.val,h⟩
       else Classical.arbitrary (Y i.val))
  refine ⟨⟨b,?_,?_⟩⟩ <;> intro i hi <;> simp [b,hi]

open Classical in
private theorem actual_projection_card_le {I O : Type*} [Fintype I] [Fintype O] {X Y Z : I → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)]
    (φ : ∀ i, X i → Y i → Z i) (G : (∀ i, Z i) → O)
    (designated B₁ B₂ P₁ P₂ : I → Prop)
    (hB : ∀ i, B₂ i → B₁ i) (hP : ∀ i, P₂ i → P₁ i)
    (hsecond : ∀ i, P₂ i → B₂ i)
    (hfirst : ∀ i, ¬designated i → B₁ i → P₁ i)
    (hordinary : ∀ i, ¬designated i →
      (∃ a : X i, Function.Surjective (φ i a)) ∧
      (∃ b : Y i, Function.Surjective (fun a => φ i a b)))
    (c : Values X Y (fun i => designated i ∧ B₁ i ∧ ¬P₁ i)
      (fun i => designated i ∧ B₂ i ∧ ¬P₂ i))
    (x : ∀ i : {i // extra designated B₁ P₁ i}, X i.val) :
    let E := extra designated B₁ P₁
    let C := {b : Values X Y B₁ B₂ // InGroup designated B₁ B₂ P₁ P₂ b c}
    let D := Values X Y (fun i => ¬B₁ i ∧ ¬E i) (fun i => ¬B₂ i ∧ ¬E i)
    let S := {z : (∀ i : {i // E i}, Z i.val) //
      z ∈ Finset.univ.filter (fun z => ∀ i, ∃ y, φ i.val (x i) y = z i)}
    let g : C → (S → D → O) := fun b z d => G (residualOutputs φ B₁ B₂ E b.val z.val d)
    Nat.card (Set.range g) ≤ Nat.card (Set.range (response φ G P₁ P₂)) := by
  classical
  dsimp only
  let E := extra designated B₁ P₁
  let C := {b : Values X Y B₁ B₂ // InGroup designated B₁ B₂ P₁ P₂ b c}
  let D := Values X Y (fun i => ¬B₁ i ∧ ¬E i) (fun i => ¬B₂ i ∧ ¬E i)
  let S := {z : (∀ i : {i // E i}, Z i.val) //
    z ∈ Finset.univ.filter (fun z => ∀ i, ∃ y, φ i.val (x i) y = z i)}
  let g : C → (S → D → O) := fun b z d => G (residualOutputs φ B₁ B₂ E b.val z.val d)
  obtain ⟨q,hq⟩ := nonnested_common_suffix_replay φ G designated B₁ B₂ P₁ P₂
    hB hP hsecond hfirst hordinary
  let f := fun b : C => response φ G P₁ P₂ (q x b.val)
  have hker : ∀ b b' : C, f b = f b' → g b = g b' := by
    intro b b' he
    funext z d
    obtain ⟨s,hs⟩ := hq c x z.val d (Finset.mem_filter.mp z.property).2
    have hh := congrFun he s
    change response φ G P₁ P₂ (q x b.val) s =
      response φ G P₁ P₂ (q x b'.val) s at hh
    rw [hs b.val b.property,hs b'.val b'.property] at hh
    exact hh
  let F := Set.range f
  let R := Set.range g
  let L := Set.range (response φ G P₁ P₂)
  let chooseB : F → C := fun t => Classical.choose t.property
  have hchoose : ∀ t, f (chooseB t) = t.val := fun t => Classical.choose_spec t.property
  let toR : F → R := fun t => ⟨g (chooseB t),Set.mem_range_self _⟩
  have hsur : Function.Surjective toR := by
    intro r
    obtain ⟨b,hb⟩ := r.property
    refine ⟨⟨f b,Set.mem_range_self _⟩,?_⟩
    apply Subtype.ext
    change g (chooseB ⟨f b,Set.mem_range_self _⟩) = r.val
    rw [hker _ b (hchoose _),hb]
  let toL : F → L := fun t => ⟨t.val,by
    obtain ⟨b,hb⟩ := t.property
    exact ⟨q x b.val,hb⟩⟩
  have hinj : Function.Injective toL := by
    intro u v he
    exact Subtype.ext (congrArg (fun t : L => t.val) he)
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype R := Fintype.ofFinite R
  letI : Fintype L := Fintype.ofFinite L
  change Nat.card R ≤ Nat.card L
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_le_of_surjective toR hsur).trans (Fintype.card_le_of_injective toL hinj)

private theorem full_suffix_factorization {I O : Type*} {X Y Z : I → Type*}
    (φ : ∀ i, X i → Y i → Z i) (G : (∀ i, Z i) → O)
    (A B₁ B₂ P₁ : I → Prop) (hB : ∀ i, B₂ i → B₁ i)
    (hφ : ∀ i, A i → ∀ z, ∃ x y, φ i x y = z) :
    let E := extra A B₁ P₁
    ∃ σ : Values X Y (fun i => ¬B₁ i) (fun i => ¬B₂ i) →
        ((∀ i : {i // E i}, Z i.val) ×
          Values X Y (fun i => ¬B₁ i ∧ ¬E i) (fun i => ¬B₂ i ∧ ¬E i)),
      Function.Surjective σ ∧
      ∀ (b : Values X Y B₁ B₂) (s : Values X Y (fun i => ¬B₁ i) (fun i => ¬B₂ i)),
        response φ G B₁ B₂ b s = G (residualOutputs φ B₁ B₂ E b (σ s).1 (σ s).2) := by
  classical
  let E := extra A B₁ P₁
  let σ : Values X Y (fun i => ¬B₁ i) (fun i => ¬B₂ i) →
      ((∀ i : {i // E i}, Z i.val) ×
        Values X Y (fun i => ¬B₁ i ∧ ¬E i) (fun i => ¬B₂ i ∧ ¬E i)) := fun s =>
    ((fun i => φ i.val (s.1 ⟨i.val,i.property.2.1⟩)
      (s.2 ⟨i.val,fun h => i.property.2.1 (hB i.val h)⟩)),
      ((fun i => s.1 ⟨i.val,i.property.1⟩), (fun i => s.2 ⟨i.val,i.property.1⟩)))
  refine ⟨σ,?_,?_⟩
  · intro zd
    let a : ∀ i : {i // E i}, X i.val := fun i => Classical.choose (hφ i.val i.property.1 (zd.1 i))
    let t : ∀ i : {i // E i}, Y i.val := fun i => Classical.choose
      (Classical.choose_spec (hφ i.val i.property.1 (zd.1 i)))
    have hs : ∀ i : {i // E i}, φ i.val (a i) (t i) = zd.1 i := fun i =>
      Classical.choose_spec (Classical.choose_spec (hφ i.val i.property.1 (zd.1 i)))
    let s : Values X Y (fun i => ¬B₁ i) (fun i => ¬B₂ i) :=
      ((fun i => if he : E i.val then a ⟨i.val,he⟩ else zd.2.1 ⟨i.val,i.property,he⟩),
       (fun i => if he : E i.val then t ⟨i.val,he⟩ else zd.2.2 ⟨i.val,i.property,he⟩))
    refine ⟨s,?_⟩
    apply Prod.ext
    · funext i
      simpa [σ,s,i.property] using hs i
    · apply Prod.ext
      · funext i; simp [σ,s,i.property.2] <;> rfl
      · funext i; simp [σ,s,i.property.2] <;> rfl
  · intro b s
    apply congrArg G
    funext i
    by_cases he : E i
    · have hb₁ : ¬B₁ i := he.2.1
      have hb₂ : ¬B₂ i := fun h => hb₁ (hB i h)
      simp [response,outputs,residualOutputs,σ,E,extra,he,hb₁,hb₂]
    · by_cases hb₁ : B₁ i <;> by_cases hb₂ : B₂ i
      all_goals try { exfalso; exact hb₁ (hB i hb₂) }
      all_goals simp [response,outputs,residualOutputs,σ,E,extra,he,hb₁,hb₂]


open Classical in
/-- Actual grouped responses are bounded using one relation law and the same task's replay. -/
theorem grouped_response_bound {I O : Type*} [Fintype I] [Fintype O] {X Y Z : I → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)]
    (φ : ∀ i, X i → Y i → Z i) (G : (∀ i, Z i) → O)
    (designated B₁ B₂ P₁ P₂ : I → Prop)
    (hB : ∀ i, B₂ i → B₁ i) (hP : ∀ i, P₂ i → P₁ i)
    (hsecond : ∀ i, P₂ i → B₂ i)
    (hfirst : ∀ i, ¬designated i → B₁ i → P₁ i)
    (hordinary : ∀ i, ¬designated i →
      (∃ a : X i, Function.Surjective (φ i a)) ∧
      (∃ b : Y i, Function.Surjective (fun a => φ i a b)))
    (hφ : ∀ i, designated i → ∀ z, ∃ x y, φ i x y = z)
    (c : Values X Y (fun i => designated i ∧ B₁ i ∧ ¬P₁ i)
      (fun i => designated i ∧ B₂ i ∧ ¬P₂ i))
    (w : (∀ i : {i // extra designated B₁ P₁ i}, X i.val) → ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hcover : ∀ z : (∀ i : {i // extra designated B₁ P₁ i}, Z i.val),
      1 ≤ ∑ x, if (∀ i, ∃ y, φ i.val (x i) y = z i) then w x else 0) :
    let C := {b : Values X Y B₁ B₂ // InGroup designated B₁ B₂ P₁ P₂ b c}
    (Nat.card (Set.range (fun b : C => response φ G B₁ B₂ b.val)) : ℝ) ≤
      (Nat.card (Set.range (response φ G P₁ P₂)) : ℝ) ^ (∑ x, w x) := by
  classical
  let E := extra designated B₁ P₁
  let C := {b : Values X Y B₁ B₂ // InGroup designated B₁ B₂ P₁ P₂ b c}
  let D := Values X Y (fun i => ¬B₁ i ∧ ¬E i) (fun i => ¬B₂ i ∧ ¬E i)
  let Attr := (∀ i : {i // E i}, Z i.val)
  let Row := (∀ i : {i // E i}, X i.val)
  let H : C → Attr → D → O := fun b z d => G (residualOutputs φ B₁ B₂ E b.val z d)
  let J := fun b : C => response φ G B₁ B₂ b.val
  let S : Row → Finset Attr := fun x => Finset.univ.filter (fun z =>
    ∀ i, ∃ y, φ i.val (x i) y = z i)
  letI : Fintype C := Fintype.ofFinite _
  letI : Fintype D := Fintype.ofFinite _
  letI : Nonempty C := actual_group_nonempty designated B₁ B₂ P₁ P₂ c
  have hc := fractional_relation_log_bound H S w hw (by
    intro z; simpa [S] using hcover z)
  have hproj : ∀ x, Nat.card (Set.range (coordinateTuple (fun z b => H b z) (S x))) ≤
      Nat.card (Set.range (response φ G P₁ P₂)) := by
    intro x
    exact actual_projection_card_le φ G designated B₁ B₂ P₁ P₂
      hB hP hsecond hfirst hordinary c x
  let K := Nat.card (Set.range (response φ G P₁ P₂))
  have kpos : (0 : ℝ) < K := by
    letI : Fintype (Set.range (response φ G P₁ P₂)) := Fintype.ofFinite _
    letI : Nonempty (Set.range (response φ G P₁ P₂)) :=
      ⟨⟨response φ G P₁ P₂ (Classical.arbitrary _),Set.mem_range_self _⟩⟩
    change 0 < (Nat.card (Set.range (response φ G P₁ P₂)) : ℝ)
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_pos
  have hrow : ∀ x, Real.log (Nat.card (Set.range
      (coordinateTuple (fun z b => H b z) (S x)))) ≤ Real.log K := by
    intro x
    let f := coordinateTuple (fun z b => H b z) (S x)
    letI : Fintype (Set.range f) := Fintype.ofFinite _
    letI : Nonempty (Set.range f) := ⟨⟨f (Classical.arbitrary C),Set.mem_range_self _⟩⟩
    have hpos : (0 : ℝ) < Nat.card (Set.range f) := by
      rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_pos
    exact Real.log_le_log hpos (by exact_mod_cast hproj x)
  have hlog : Real.log (Nat.card (Set.range H)) ≤ (∑ x, w x) * Real.log K := by
    calc
      _ ≤ ∑ x, w x * Real.log (Nat.card (Set.range
        (coordinateTuple (fun z b => H b z) (S x)))) := hc
      _ ≤ ∑ x, w x * Real.log K := Finset.sum_le_sum
        (fun x _ => mul_le_mul_of_nonneg_left (hrow x) (hw x))
      _ = _ := (Finset.sum_mul ..).symm
  have hpos : (0 : ℝ) < Nat.card (Set.range H) := by
    letI : Fintype (Set.range H) := Fintype.ofFinite _
    letI : Nonempty (Set.range H) := ⟨⟨H (Classical.arbitrary C),Set.mem_range_self _⟩⟩
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_pos
  have hb : (Nat.card (Set.range H) : ℝ) ≤ (K : ℝ) ^ (∑ x, w x) := by
    apply (Real.log_le_log_iff hpos (Real.rpow_pos_of_pos kpos _)).1
    simpa only [Real.log_rpow kpos] using hlog
  obtain ⟨sigma,hsur,hsigma⟩ := full_suffix_factorization φ G designated B₁ B₂ P₁ hB hφ
  have hjh : ∀ b b' : C, J b = J b' → H b = H b' := by
    intro b b' he
    funext z d
    obtain ⟨s,hs⟩ := hsur (z,d)
    have hv := congrFun he s
    dsimp [J] at hv
    rw [hsigma b.val s,hsigma b'.val s,hs] at hv
    exact hv
  have hhj : ∀ b b' : C, H b = H b' → J b = J b' := by
    intro b b' he
    funext s
    dsimp [J]
    rw [hsigma b.val s,hsigma b'.val s]
    exact congrFun (congrFun he (sigma s).1) (sigma s).2
  have heq : Nat.card (Set.range J) = Nat.card (Set.range H) :=
    le_antisymm (range_card_le_of_kernel H J hhj) (range_card_le_of_kernel J H hjh)
  change (Nat.card (Set.range J) : ℝ) ≤ (K : ℝ) ^ (∑ x, w x)
  rw [heq]
  exact hb


/-- A rational optimal cover supplied by the existing real-optimal certificate theorem. -/
noncomputable def optimalRowCover {X Y Z : Type*} [Fintype X] [Fintype Z]
    [Nonempty X] [Nonempty Y] (φ : X → Y → Z) (hφ : ∀ z, ∃ x y, φ x y = z) : X → ℚ := by
  classical
  letI : Nonempty Z := ⟨φ (Classical.arbitrary X) (Classical.arbitrary Y)⟩
  exact Classical.choose (row_image_rational_duality φ hφ)

noncomputable def rowCoverNumber {X Y Z : Type*} [Fintype X] [Fintype Z]
    [Nonempty X] [Nonempty Y] (φ : X → Y → Z) (hφ : ∀ z, ∃ x y, φ x y = z) : ℝ :=
  ∑ x, (optimalRowCover φ hφ x : ℝ)

open Classical in
private theorem optimal_row_cover_spec {X Y Z : Type*} [Fintype X] [Fintype Z]
    [Nonempty X] [Nonempty Y] (φ : X → Y → Z) (hφ : ∀ z, ∃ x y, φ x y = z) :
    ∃ w : Z → ℚ,
      (∀ x, 0 ≤ optimalRowCover φ hφ x) ∧
      (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then optimalRowCover φ hφ x else 0) ∧
      (∀ z, 0 ≤ w z) ∧
      (∀ x, (∑ z, if (∃ y, φ x y = z) then w z else 0) ≤ 1) ∧
      (∑ x, optimalRowCover φ hφ x) = (∑ z, w z) ∧
      (∀ μ : X → ℝ, (∀ x, 0 ≤ μ x) →
        (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then μ x else 0) →
        rowCoverNumber φ hφ ≤ ∑ x, μ x) ∧
      (∀ v : Z → ℝ, (∀ z, 0 ≤ v z) →
        (∀ x, (∑ z, if (∃ y, φ x y = z) then v z else 0) ≤ 1) →
        (∑ z, v z) ≤ rowCoverNumber φ hφ) := by
  classical
  letI : Nonempty Z := ⟨φ (Classical.arbitrary X) (Classical.arbitrary Y)⟩
  obtain ⟨w,hn,hc,hw,hl,he,hm,hmax⟩ := Classical.choose_spec (row_image_rational_duality φ hφ)
  refine ⟨w,hn,hc,hw,hl,he,hm,?_⟩
  intro v hv hc
  have h := hmax v hv hc
  have eq : (∑ z, (w z : ℝ)) = rowCoverNumber φ hφ := by
    dsimp [rowCoverNumber,optimalRowCover]
    exact_mod_cast he.symm
  rwa [eq] at h

open Classical in
private theorem product_cover_value {J : Type*} [Fintype J] [DecidableEq J] {X Y Z : J → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)]
    (φ : ∀ i, X i → Y i → Z i) (hφ : ∀ i z, ∃ x y, φ i x y = z)
    (hprod : ∀ z : (∀ i, Z i), ∃ (x : ∀ i, X i) (y : ∀ i, Y i), (fun i => φ i (x i) (y i)) = z) :
    rowCoverNumber (fun (x : ∀ i, X i) (y : ∀ i, Y i) i => φ i (x i) (y i)) hprod =
      ∏ i, rowCoverNumber (φ i) (hφ i) := by
  classical
  choose dual hn hc hd hl he hm hmax using fun i => optimal_row_cover_spec (φ i) (hφ i)
  let lam : (∀ i, X i) → ℝ := fun x => ∏ i, (optimalRowCover (φ i) (hφ i) (x i) : ℝ)
  let v : (∀ i, Z i) → ℝ := fun z => ∏ i, (dual i (z i) : ℝ)
  have incidence (x : ∀ i, X i) (z : ∀ i, Z i) :
      (∃ y : ∀ i, Y i, (fun i => φ i (x i) (y i)) = z) ↔ ∀ i, ∃ y, φ i (x i) y = z i := by
    constructor
    · rintro ⟨y,hy⟩ i; exact ⟨y i,congrFun hy i⟩
    · intro h
      choose y hy using h
      exact ⟨y,funext hy⟩
  have hln : ∀ x, 0 ≤ lam x := fun x => Finset.prod_nonneg
    (fun i _ => by exact_mod_cast hn i (x i))
  have hvn : ∀ z, 0 ≤ v z := fun z => Finset.prod_nonneg
    (fun i _ => by exact_mod_cast hd i (z i))
  have hcoverage : ∀ z : (∀ i, Z i), 1 ≤ ∑ x, if (∃ y : ∀ i, Y i, (fun i => φ i (x i) (y i)) = z) then lam x else 0 := by
    intro z
    have eq : (∑ x, if (∀ i, ∃ y, φ i (x i) y = z i) then lam x else 0) =
        ∏ i, ∑ x, if (∃ y, φ i x y = z i) then (optimalRowCover (φ i) (hφ i) x : ℝ) else 0 := by
      simp only [lam,← Fintype.prod_ite_zero]
      exact (Fintype.prod_sum (fun i x => if (∃ y, φ i x y = z i) then
        (optimalRowCover (φ i) (hφ i) x : ℝ) else 0)).symm
    simp_rw [incidence]
    rw [eq]
    apply Finset.one_le_prod
    intro i hi
    have hh : (1 : ℝ) ≤ ((∑ x, if (∃ y, φ i x y = z i) then
        optimalRowCover (φ i) (hφ i) x else 0 : ℚ) : ℝ) := by exact_mod_cast hc i (z i)
    have eq : ((∑ x, if (∃ y, φ i x y = z i) then
        optimalRowCover (φ i) (hφ i) x else 0 : ℚ) : ℝ) =
        ∑ x, if (∃ y, φ i x y = z i) then (optimalRowCover (φ i) (hφ i) x : ℝ) else 0 := by
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro x hx; split_ifs <;> simp
    rwa [eq] at hh
  have hpacking : ∀ x : (∀ i, X i), (∑ z, if (∃ y : ∀ i, Y i, (fun i => φ i (x i) (y i)) = z) then v z else 0) ≤ 1 := by
    intro x
    have eq : (∑ z, if (∀ i, ∃ y, φ i (x i) y = z i) then v z else 0) =
        ∏ i, ∑ z, if (∃ y, φ i (x i) y = z) then (dual i z : ℝ) else 0 := by
      simp only [v,← Fintype.prod_ite_zero]
      exact (Fintype.prod_sum (fun i z => if (∃ y, φ i (x i) y = z) then
        (dual i z : ℝ) else 0)).symm
    simp_rw [incidence]
    rw [eq]
    apply Finset.prod_le_one
    · intro i hi; exact Finset.sum_nonneg (fun z _ => by split_ifs; exact_mod_cast hd i z; exact le_rfl)
    · intro i hi
      have hh : ((∑ z, if (∃ y, φ i (x i) y = z) then dual i z else 0 : ℚ) : ℝ) ≤ 1 := by
        exact_mod_cast hl i (x i)
      have eq : ((∑ z, if (∃ y, φ i (x i) y = z) then dual i z else 0 : ℚ) : ℝ) =
          ∑ z, if (∃ y, φ i (x i) y = z) then (dual i z : ℝ) else 0 := by
        rw [Rat.cast_sum]
        apply Finset.sum_congr rfl
        intro z hz; split_ifs <;> simp
      rwa [eq] at hh
  have hlamval : (∑ x, lam x) = ∏ i, rowCoverNumber (φ i) (hφ i) := by
    exact (Fintype.prod_sum (fun i x => (optimalRowCover (φ i) (hφ i) x : ℝ))).symm
  have hvval : (∑ z, v z) = ∏ i, rowCoverNumber (φ i) (hφ i) := by
    rw [show (∑ z, v z) = ∏ i, ∑ z, (dual i z : ℝ) from (Fintype.prod_sum (fun i z => (dual i z : ℝ))).symm]
    apply Finset.prod_congr rfl
    intro i hi
    dsimp [rowCoverNumber]
    exact_mod_cast (he i).symm
  obtain ⟨pd,pn,pc,pdn,pdc,peq,pmin,pmax⟩ :=
    optimal_row_cover_spec (fun (x : ∀ i, X i) (y : ∀ i, Y i) i => φ i (x i) (y i)) hprod
  apply le_antisymm
  · apply le_trans (pmin lam hln ?_) hlamval.le
    intro z
    convert hcoverage z using 1
    congr 1
    funext x
    split_ifs <;> rfl
  · apply le_trans hvval.ge (pmax v hvn ?_)
    intro x
    convert hpacking x using 1
    congr 1
    funext z
    split_ifs <;> rfl

open Classical in
/-- The per-group bound uses the attained actual product optimum, equal to the factor product. -/
theorem grouped_optimal_product_bound {I O : Type*} [Fintype I] [Fintype O] {X Y Z : I → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)]
    (φ : ∀ i, X i → Y i → Z i) (G : (∀ i, Z i) → O)
    (designated B₁ B₂ P₁ P₂ : I → Prop)
    (hB : ∀ i, B₂ i → B₁ i) (hP : ∀ i, P₂ i → P₁ i)
    (hsecond : ∀ i, P₂ i → B₂ i)
    (hfirst : ∀ i, ¬designated i → B₁ i → P₁ i)
    (hordinary : ∀ i, ¬designated i →
      (∃ a : X i, Function.Surjective (φ i a)) ∧
      (∃ b : Y i, Function.Surjective (fun a => φ i a b)))
    (hφ : ∀ i, designated i → ∀ z, ∃ x y, φ i x y = z)
    (c : Values X Y (fun i => designated i ∧ B₁ i ∧ ¬P₁ i)
      (fun i => designated i ∧ B₂ i ∧ ¬P₂ i)) :
    let E := extra designated B₁ P₁
    let C := {b : Values X Y B₁ B₂ // InGroup designated B₁ B₂ P₁ P₂ b c}
    (Nat.card (Set.range (fun b : C => response φ G B₁ B₂ b.val)) : ℝ) ≤
      (Nat.card (Set.range (response φ G P₁ P₂)) : ℝ) ^
        (∏ i : {i // E i}, rowCoverNumber (φ i.val) (hφ i.val i.property.1)) := by
  classical
  let E := extra designated B₁ P₁
  let prodφ := fun (x : ∀ i : {i // E i}, X i.val) (y : ∀ i : {i // E i}, Y i.val)
    i => φ i.val (x i) (y i)
  have hprod : ∀ z, ∃ x y, prodφ x y = z := by
    intro z
    choose x y h using fun i : {i // E i} => hφ i.val i.property.1 (z i)
    exact ⟨x,y,funext h⟩
  let lam := optimalRowCover prodφ hprod
  obtain ⟨dual,hn,hc,hd,hl,he,hm,hmax⟩ := optimal_row_cover_spec prodφ hprod
  have hbound := grouped_response_bound φ G designated B₁ B₂ P₁ P₂
    hB hP hsecond hfirst hordinary hφ c (fun x => (lam x : ℝ))
    (fun x => by exact_mod_cast hn x) (by
      intro z
      have h : (1 : ℝ) ≤ ∑ x, if (∃ y, prodφ x y = z) then (lam x : ℝ) else 0 := by
        have hh : (1 : ℝ) ≤ ((∑ x, if (∃ y, prodφ x y = z) then lam x else 0 : ℚ) : ℝ) := by
          exact_mod_cast hc z
        have eq : ((∑ x, if (∃ y, prodφ x y = z) then lam x else 0 : ℚ) : ℝ) =
            ∑ x, if (∃ y, prodφ x y = z) then (lam x : ℝ) else 0 := by
          rw [Rat.cast_sum]
          apply Finset.sum_congr rfl
          intro x hx; split_ifs <;> simp
        rwa [eq] at hh
      have eq : ∀ x, (∃ y, prodφ x y = z) ↔ ∀ i, ∃ y, φ i.val (x i) y = z i := by
        intro x
        constructor
        · rintro ⟨y,hy⟩ i; exact ⟨y i,congrFun hy i⟩
        · intro hh; choose y hy using hh; exact ⟨y,funext hy⟩
      have heq : (∑ x, if (∃ y, prodφ x y = z) then (lam x : ℝ) else 0) =
          ∑ x, if (∀ i, ∃ y, φ i.val (x i) y = z i) then (lam x : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hi : ∃ y, prodφ x y = z
        · rw [if_pos hi,if_pos ((eq x).mp hi)]
        · have hn : ¬(∀ i, ∃ y, φ i.val (x i) y = z i) := fun e => hi ((eq x).mpr e)
          rw [if_neg hi,if_neg hn]
      rwa [heq] at h)
  have hval := product_cover_value (fun i : {i // E i} => φ i.val)
    (fun i => hφ i.val i.property.1) hprod
  change rowCoverNumber prodφ hprod = _ at hval
  change _ ≤ _ ^ rowCoverNumber prodφ hprod at hbound
  rw [hval] at hbound
  exact hbound


private theorem range_card_le_sum_groups {B C O : Type*} [Fintype B] [Fintype C] [Fintype O]
    (f : B → O) (group : B → C → Prop) (label : B → C) (hl : ∀ b, group b (label b)) :
    Nat.card (Set.range f) ≤ ∑ c, Nat.card (Set.range (fun b : {b // group b c} => f b.val)) := by
  classical
  let R : C → Type _ := fun c => ↥(Set.range (fun b : {b // group b c} => f b.val))
  letI : ∀ c, Fintype (R c) := fun c => Fintype.ofFinite _
  let chooseB : Set.range f → B := fun r => Classical.choose r.property
  have hs : ∀ r, f (chooseB r) = r.val := fun r => Classical.choose_spec r.property
  let toSigma : Set.range f → Sigma R := fun r =>
    ⟨label (chooseB r),⟨f (chooseB r),⟨⟨chooseB r,hl _⟩,rfl⟩⟩⟩
  have hi : Function.Injective toSigma := by
    intro r r' he
    have h := congrArg (fun t : Sigma R => t.2.val) he
    change f (chooseB r) = f (chooseB r') at h
    rw [hs,hs] at h
    exact Subtype.ext h
  letI : Fintype (Set.range f) := Fintype.ofFinite _
  have hc := Fintype.card_le_of_injective toSigma hi
  simpa only [Fintype.card_sigma,Nat.card_eq_fintype_card] using hc

open Classical in
/-- The whole actual cut is the union of its designated-only groups. -/
theorem nonnested_cut_product_bound {I O : Type*} [Fintype I] [Fintype O] {X Y Z : I → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)]
    (φ : ∀ i, X i → Y i → Z i) (G : (∀ i, Z i) → O)
    (designated B₁ B₂ P₁ P₂ : I → Prop)
    (hB : ∀ i, B₂ i → B₁ i) (hP : ∀ i, P₂ i → P₁ i)
    (hsecond : ∀ i, P₂ i → B₂ i)
    (hfirst : ∀ i, ¬designated i → B₁ i → P₁ i)
    (hordinary : ∀ i, ¬designated i →
      (∃ a : X i, Function.Surjective (φ i a)) ∧
      (∃ b : Y i, Function.Surjective (fun a => φ i a b)))
    (hφ : ∀ i, designated i → ∀ z, ∃ x y, φ i x y = z) :
    let E := extra designated B₁ P₁
    let Q := Values X Y (fun i => designated i ∧ B₁ i ∧ ¬P₁ i)
      (fun i => designated i ∧ B₂ i ∧ ¬P₂ i)
    (Nat.card (Set.range (response φ G B₁ B₂)) : ℝ) ≤
      (Nat.card Q : ℝ) * (Nat.card (Set.range (response φ G P₁ P₂)) : ℝ) ^
        (∏ i : {i // E i}, rowCoverNumber (φ i.val) (hφ i.val i.property.1)) := by
  classical
  let E := extra designated B₁ P₁
  let Q := Values X Y (fun i => designated i ∧ B₁ i ∧ ¬P₁ i)
      (fun i => designated i ∧ B₂ i ∧ ¬P₂ i)
  let B := Values X Y B₁ B₂
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype Q := Fintype.ofFinite _
  let Suffix := Values X Y (fun i => ¬B₁ i) (fun i => ¬B₂ i)
  letI : Fintype Suffix := Fintype.ofFinite _
  let label : B → Q := fun b =>
    ((fun i => b.1 ⟨i.val,i.property.2.1⟩),(fun i => b.2 ⟨i.val,i.property.2.1⟩))
  have hl : ∀ b : B, InGroup designated B₁ B₂ P₁ P₂ b (label b) := by
    intro b; constructor <;> intro i hi <;> rfl
  have hc := range_card_le_sum_groups (response φ G B₁ B₂)
    (fun b c => InGroup designated B₁ B₂ P₁ P₂ b c) label hl
  have hs : (Nat.card (Set.range (response φ G B₁ B₂)) : ℝ) ≤
      ∑ c : Q, (Nat.card (Set.range (fun b : {b : B // InGroup designated B₁ B₂ P₁ P₂ b c} =>
        response φ G B₁ B₂ b.val)) : ℝ) := by exact_mod_cast hc
  calc
    _ ≤ ∑ c : Q, (Nat.card (Set.range (fun b : {b : B // InGroup designated B₁ B₂ P₁ P₂ b c} =>
        response φ G B₁ B₂ b.val)) : ℝ) := hs
    _ ≤ ∑ c : Q, (Nat.card (Set.range (response φ G P₁ P₂)) : ℝ) ^
        (∏ i : {i // E i}, rowCoverNumber (φ i.val) (hφ i.val i.property.1)) :=
      Finset.sum_le_sum (fun c _ => grouped_optimal_product_bound φ G designated B₁ B₂ P₁ P₂
        hB hP hsecond hfirst hordinary hφ c)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [← Nat.card_eq_fintype_card]

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

private theorem second_implies_first (s : Skeleton I) (c : Cut I) :
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
private theorem raw_second_implies_first (s : Skeleton I) (t : ℕ) :
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

/- Further actual upper-bound consumers follow in CompletionUpperBounds.lean.
This fragment does not assert the scalar Boolean sharpness construction. -/
end CompletionSorting

section CompletionSorting
variable {I O : Type} [Fintype I] [Fintype O] {X Y Z : I → Type}
  [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)] [∀ i,Fintype (Z i)]
  [∀ i,Nonempty (X i)] [∀ i,Nonempty (Y i)]

noncomputable def cutCard (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O)
    (l r : I → Prop) : ℕ := Nat.card (Set.range (response φ G l r))

noncomputable def width (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O)
    (p : Endpoint I ≃ Fin (2*Fintype.card I)) : ℕ := by
  classical
  exact (Finset.range (2*Fintype.card I+1)).sup (fun t =>
    cutCard φ G (fun i => (p (i,false)).val < t) (fun i => (p (i,true)).val < t))

private theorem cut_pos (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O) (l r : I → Prop) :
    1 ≤ cutCard φ G l r := by
  classical
  let b : Values X Y l r := (fun _ => Classical.choice inferInstance,fun _ => Classical.choice inferInstance)
  letI : Nonempty (Set.range (response φ G l r)) := ⟨⟨response φ G l r b,Set.mem_range_self _⟩⟩
  exact Nat.card_pos

private theorem width_contains (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O)
    (p : Endpoint I ≃ Fin (2*Fintype.card I)) (t : ℕ) (ht : t ≤ 2*Fintype.card I) :
    cutCard φ G (fun i => (p (i,false)).val < t) (fun i => (p (i,true)).val < t) ≤ width φ G p := by
  classical
  exact Finset.le_sup (f := fun t => cutCard φ G (fun i => (p (i,false)).val < t) (fun i => (p (i,true)).val < t)) (Finset.mem_range.mpr (by omega))

private theorem width_pos (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O)
    (p : Endpoint I ≃ Fin (2*Fintype.card I)) : 1 ≤ width φ G p :=
  (cut_pos φ G _ _).trans (width_contains φ G p 0 (by omega))

private theorem width_le_of_layers (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O)
    (p : Endpoint I ≃ Fin (2*Fintype.card I)) (bound : ℝ)
    (hb : ∀ t, t ≤ 2*Fintype.card I → (cutCard φ G (fun i => (p (i,false)).val < t) (fun i => (p (i,true)).val < t) : ℝ) ≤ bound) :
    (width φ G p : ℝ) ≤ bound := by
  classical
  let f := fun t => cutCard φ G (fun i => (p (i,false)).val < t) (fun i => (p (i,true)).val < t)
  let layers := Finset.range (2*Fintype.card I+1)
  obtain ⟨t,ht,hmax⟩ := Finset.exists_max_image layers f ⟨0,by simp [layers]⟩
  have hw : width φ G p=f t := by
    apply le_antisymm
    · exact Finset.sup_le (fun j hj => hmax j hj)
    · exact Finset.le_sup ht
  rw [hw]
  exact hb t (by have h:=Finset.mem_range.mp ht; omega)

/-- Each original normalized layer is transported to one exact pair predicate cut. -/
private theorem normalized_card_transport (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O)
    (s : Skeleton I) (c : Cut I) :
    Nat.card (Set.range (labelledResponse φ G (fun v => (s.completion v).val < cutSize s c))) =
      cutCard φ G (firstRead s c) (secondRead s c) := by
  rw [labelled_response_card]
  obtain ⟨_,h1,h2⟩ := completion_prefix s c
  have he1 : (fun i => (s.completion (i,false)).val < cutSize s c)=firstRead s c :=
    funext (fun i => propext (h1 i))
  have he2 : (fun i => (s.completion (i,true)).val < cutSize s c)=secondRead s c :=
    funext (fun i => propext (h2 i))
  change cutCard φ G (fun i => (s.completion (i,false)).val < cutSize s c) (fun i => (s.completion (i,true)).val < cutSize s c) = _
  rw [he1,he2]

/-- Initial/constant capacities are exactly one; no nonconstant-task premise is used. -/
theorem initial_and_constant_layers (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O) :
    cutCard φ G (fun _ => False) (fun _ => False)=1 ∧
    (∀ (o : O) (l r : I → Prop), cutCard φ (fun _ => o) l r=1) := by
  classical
  constructor
  · let b0 : Values X Y (fun _ => False) (fun _ => False) :=
      (fun i => False.elim i.property,fun i => False.elim i.property)
    have he : Set.range (response φ G (fun _ => False) (fun _ => False))=
        {response φ G (fun _ => False) (fun _ => False) b0} := by
      ext r; constructor
      · rintro ⟨b,rfl⟩
        have hb : b=b0 := by apply Prod.ext <;> funext i <;> exact False.elim i.property
        simp [hb]
      · intro h; have hr := Set.mem_singleton_iff.mp h; exact ⟨b0,hr.symm⟩
    simp [cutCard,he]
  · intro o l r
    have h : response φ (fun _ => o) l r=(fun _ => (fun _ => o)) := rfl
    simp [cutCard,h,Set.range_const]

/-- At the full original layer, evaluation on the unique empty suffix is exact. -/
theorem terminal_layer (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O) :
    cutCard φ G (fun _ => True) (fun _ => True)=
      Nat.card (Set.range (fun b : Values X Y (fun _ => True) (fun _ => True) =>
        G (fun i => φ i (b.1 ⟨i,trivial⟩) (b.2 ⟨i,trivial⟩)))) := by
  classical
  let f := response φ G (fun _ => True) (fun _ => True)
  let g := fun b : Values X Y (fun _ => True) (fun _ => True) =>
    G (fun i => φ i (b.1 ⟨i,trivial⟩) (b.2 ⟨i,trivial⟩))
  have hg : ∀ b q, f b q=g b := by
    intro b q
    apply congrArg G
    funext i
    simp [f,g,response,outputs]
  have hfg : ∀ b b', f b=f b' → g b=g b' := by
    intro b b' h
    let q : Values X Y (fun _ => ¬True) (fun _ => ¬True) :=
      (fun i => False.elim (i.property trivial),fun i => False.elim (i.property trivial))
    simpa only [hg] using congrFun h q
  have hgf : ∀ b b', g b=g b' → f b=f b' := by
    intro b b' h; funext q; simpa only [hg] using h
  exact le_antisymm (range_card_le_of_kernel g f hgf) (range_card_le_of_kernel f g hfg)

/-- The original fixed coefficient D, as the cardinal of all designated raw values. -/
noncomputable def designatedSize (designated : I → Prop) : ℕ :=
  Nat.card (Values X Y designated designated)

private theorem designated_size_formula (designated : I → Prop) :
    designatedSize (X:=X) (Y:=Y) designated =
      ∏ i : {i // designated i}, Fintype.card (X i.val)*Fintype.card (Y i.val) := by
  classical
  simp [designatedSize,Values,Nat.card_eq_fintype_card,Fintype.card_pi,Finset.prod_mul_distrib]

/-- Fill only missing designated coordinates to inject each actual group label into D. -/
private theorem group_card_le_designated (designated l r p q : I → Prop) :
    Nat.card (Values X Y (fun i => designated i ∧ l i ∧ ¬p i)
      (fun i => designated i ∧ r i ∧ ¬q i)) ≤ designatedSize (X:=X) (Y:=Y) designated := by
  classical
  let A := Values X Y (fun i => designated i ∧ l i ∧ ¬p i)
    (fun i => designated i ∧ r i ∧ ¬q i)
  let B := Values X Y designated designated
  let fill : A → B := fun a =>
    (fun i => if h : l i.val ∧ ¬p i.val then a.1 ⟨i.val,i.property,h⟩ else Classical.choice inferInstance,
     fun i => if h : r i.val ∧ ¬q i.val then a.2 ⟨i.val,i.property,h⟩ else Classical.choice inferInstance)
  have hi : Function.Injective fill := by
    intro a b h
    apply Prod.ext
    · funext i
      have he := congrFun (congrArg Prod.fst h) ⟨i.val,i.property.1⟩
      simpa [fill,i.property.2] using he
    · funext i
      have he := congrFun (congrArg Prod.snd h) ⟨i.val,i.property.1⟩
      simpa [fill,i.property.2] using he
  letI : Fintype A := Fintype.ofFinite _
  letI : Fintype B := Fintype.ofFinite _
  simpa only [designatedSize,Nat.card_eq_fintype_card] using Fintype.card_le_of_injective fill hi

noncomputable def productOn (P : I → Prop) (τ : I → ℝ) : ℝ := by
  classical
  exact ∏ i, if P i then τ i else 1

private theorem productOn_subtype (P : I → Prop) (τ : I → ℝ) :
    (∏ i : {i // P i}, τ i.val)=productOn P τ := by
  classical
  have h := Finset.prod_subtype (p := P) (F := inferInstance) (Finset.univ.filter P)
    (by intro i; simp) τ
  rw [Finset.prod_filter] at h
  exact h.symm

private theorem productOn_mono (A B : I → Prop) (τ : I → ℝ)
    (hτ : ∀ i, 1 ≤ τ i) (h : ∀ i, A i → B i) : productOn A τ ≤ productOn B τ := by
  classical
  apply Finset.prod_le_prod
  · intro i _; split_ifs <;> linarith [hτ i]
  · intro i _
    by_cases ha : A i
    · simp [ha,h i ha]
    · by_cases hb : B i <;> simp [ha,hb,hτ i]

private theorem productOn_one_le (P : I → Prop) (τ : I → ℝ) (hτ : ∀ i,1 ≤ τ i) :
    1 ≤ productOn P τ := by
  have h := productOn_mono (fun _ => False) P τ hτ (fun _ h => h.elim)
  simpa [productOn] using h

/-- Actual optimal values supplied by the preserved A11 rational/real LP stack. -/
noncomputable def actualTau (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z) (i : I) : ℝ :=
  rowCoverNumber (φ i) (hφ i)

private theorem actualTau_one_le (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z) :
    ∀ i,1 ≤ actualTau φ hφ i := by
  classical
  intro i
  obtain ⟨w,hn,hc,_,_,_,_,_⟩ := optimal_row_cover_spec (φ i) (hφ i)
  let z := φ i (Classical.choice inferInstance) (Classical.choice inferInstance)
  have hb := hc z
  have hs : (∑ x, if (∃ y,φ i x y=z) then optimalRowCover (φ i) (hφ i) x else 0) ≤ ∑ x, optimalRowCover (φ i) (hφ i) x := by
    apply Finset.sum_le_sum
    intro x _; split_ifs <;> simp [hn x]
  have hb' : (1:ℚ) ≤ (∑ x, if (∃ y,φ i x y=z) then optimalRowCover (φ i) (hφ i) x else 0) := by
    convert hb using 1
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : ∃ y,φ i x y=z <;> simp [h]
  have hh := hb'.trans hs
  have hreal : (1:ℝ) ≤ ((∑ x,optimalRowCover (φ i) (hφ i) x : ℚ):ℝ) := by exact_mod_cast hh
  simpa [actualTau,rowCoverNumber,Rat.cast_sum] using hreal

noncomputable def theta (s : Skeleton I) (designated : I → Prop) (τ : I → ℝ)
    (hordinaryIndex : ∃ i,¬designated i) : ℝ := by
  classical
  let ordinary := Finset.univ.filter (fun i => ¬designated i)
  have hne : ordinary.Nonempty := by
    obtain ⟨i,hi⟩ := hordinaryIndex
    exact ⟨i,by simp [ordinary,hi]⟩
  exact ordinary.sup' hne (fun k => productOn (neighborhood s designated k) τ)

private theorem neighborhood_le_theta (s : Skeleton I) (designated : I → Prop) (τ : I → ℝ)
    (ho : ∃ i,¬designated i) (k : I) (hk : ¬designated k) :
    productOn (neighborhood s designated k) τ ≤ theta s designated τ ho := by
  classical
  dsimp [theta]
  exact Finset.le_sup' (fun k => productOn (neighborhood s designated k) τ) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩)

private theorem theta_one_le (s : Skeleton I) (designated : I → Prop) (τ : I → ℝ)
    (ho : ∃ i,¬designated i) (hτ : ∀ i,1 ≤ τ i) : 1 ≤ theta s designated τ ho := by
  obtain ⟨k,hk⟩ := ho
  exact (productOn_one_le _ τ hτ).trans (neighborhood_le_theta s designated τ ⟨k,hk⟩ k hk)

/-- All geometry for the D-weighted bound, with the no-touched case constructed. -/
private theorem weighted_geometry (s : Skeleton I) (designated : I → Prop) (τ : I → ℝ)
    (ho : ∃ i,¬designated i) (hτ : ∀ i,1 ≤ τ i) (c : Cut I) :
    ∃ t ≤ 2*Fintype.card I,
      (∀ i,s.second i < t → secondRead s c i) ∧
      (∀ i,¬designated i → firstRead s c i → s.first i < t) ∧
      productOn (extra designated (firstRead s c) (fun i => s.first i < t)) τ ≤ theta s designated τ ho := by
  classical
  by_cases ht : ∃ i,¬designated i ∧ firstRead s c i
  · obtain ⟨k,hk,hread,hmax,hsecond,hE⟩ := latest_touched_ordinary s designated c ht
    refine ⟨s.first k+1,by have h:=(s.position (k,false)).isLt; change s.first k < 2 * Fintype.card I at h; omega,hsecond,?_,?_⟩
    · intro i hd hi; have h:=hmax i hd hi; omega
    · exact (productOn_mono _ _ τ hτ hE).trans (neighborhood_le_theta s designated τ ho k hk)
  · refine ⟨0,by omega,?_,?_,?_⟩
    · intro i hi; omega
    · intro i hd hi; exact (ht ⟨i,hd,hi⟩).elim
    · have he : extra designated (firstRead s c) (fun i => s.first i < 0)=(fun _ => False) := by
        funext i; apply propext; simp [extra]
      rw [he]
      simpa [productOn] using theta_one_le s designated τ ho hτ

private theorem original_cut_bound (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O)
    (hφ : ∀ i z,∃ x y,φ i x y=z) (s : Skeleton I) (designated : I → Prop)
    (hordinary : ∀ i,¬designated i → (∃ a:X i,Function.Surjective (φ i a)) ∧ (∃ b:Y i,Function.Surjective (fun a => φ i a b)))
    (c : Cut I) (t : ℕ) (ht : t ≤ 2*Fintype.card I)
    (hsecond : ∀ i,s.second i < t → secondRead s c i)
    (hfirst : ∀ i,¬designated i → firstRead s c i → s.first i < t)
    (factor exponent : ℝ)
    (hfactor : (Nat.card (Values X Y
      (fun i => designated i ∧ firstRead s c i ∧ ¬s.first i < t)
      (fun i => designated i ∧ secondRead s c i ∧ ¬s.second i < t)) : ℝ) ≤ factor)
    (hfnonneg : 0 ≤ factor)
    (hexponent : productOn (extra designated (firstRead s c) (fun i => s.first i < t)) (actualTau φ hφ) ≤ exponent) :
    (cutCard φ G (firstRead s c) (secondRead s c) : ℝ) ≤ factor*(width φ G s.position : ℝ)^exponent := by
  classical
  let E := extra designated (firstRead s c) (fun i => s.first i < t)
  let power := productOn E (actualTau φ hφ)
  have h := nonnested_cut_product_bound φ G designated (firstRead s c) (secondRead s c)
    (fun i => s.first i < t) (fun i => s.second i < t)
    (second_implies_first s c) (raw_second_implies_first s t) hsecond hfirst hordinary
    (fun i _ => hφ i)
  have hp : (∏ i : {i // E i},rowCoverNumber (φ i.val) (hφ i.val))=power :=
    productOn_subtype E (actualTau φ hφ)
  change (cutCard φ G (firstRead s c) (secondRead s c) : ℝ) ≤ _*(cutCard φ G (fun i => s.first i < t) (fun i => s.second i < t) : ℝ)^_ at h
  rw [hp] at h
  have hW : (1:ℝ) ≤ width φ G s.position := by exact_mod_cast width_pos φ G s.position
  have hκ : (cutCard φ G (fun i => s.first i < t) (fun i => s.second i < t) : ℝ) ≤ width φ G s.position := by
    exact_mod_cast width_contains φ G s.position t ht
  have hp0 : 0 ≤ power := le_trans (by norm_num) (productOn_one_le E _ (actualTau_one_le φ hφ))
  have hpow := (Real.rpow_le_rpow (Nat.cast_nonneg _) hκ hp0).trans
    (Real.rpow_le_rpow_of_exponent_le hW hexponent)
  exact h.trans (mul_le_mul hfactor hpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hfnonneg)

/-- Both bounds on every normalized cut use the same actual F. -/
theorem every_normalized_cut_bounds (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O)
    (hφ : ∀ i z,∃ x y,φ i x y=z) (s : Skeleton I) (designated : I → Prop)
    (ho : ∃ i,¬designated i)
    (hordinary : ∀ i,¬designated i → (∃ a:X i,Function.Surjective (φ i a)) ∧ (∃ b:Y i,Function.Surjective (fun a => φ i a b)))
    (c : Cut I) :
    let τ:=actualTau φ hφ
    let W:=(width φ G s.position : ℝ)
    let D:=(designatedSize (X:=X) (Y:=Y) designated : ℝ)
    (cutCard φ G (firstRead s c) (secondRead s c) : ℝ) ≤ W^(productOn designated τ) ∧
    (cutCard φ G (firstRead s c) (secondRead s c) : ℝ) ≤ D*W^(theta s designated τ ho) := by
  classical
  let τ := actualTau φ hφ
  have hτ : ∀ i,1 ≤ τ i := actualTau_one_le φ hφ
  constructor
  · obtain ⟨ht,hfirst,hsecond⟩ := matched_cut_geometry s c
    let t := matchedSize s c
    have hq1 : (fun i => designated i ∧ firstRead s c i ∧ ¬s.first i < t)=(fun _ => False) := by
      funext i; apply propext; constructor
      · rintro ⟨_,hi,hn⟩; exact hn (hfirst i hi)
      · exact False.elim
    have hq2 : (fun i => designated i ∧ secondRead s c i ∧ ¬s.second i < t)=(fun _ => False) := by
      funext i; apply propext; constructor
      · rintro ⟨_,hi,hn⟩; exact hn ((hsecond i).mp hi)
      · exact False.elim
    have hq : (Nat.card (Values X Y
        (fun i => designated i ∧ firstRead s c i ∧ ¬s.first i < t)
        (fun i => designated i ∧ secondRead s c i ∧ ¬s.second i < t)) : ℝ) ≤ 1 := by
      rw [hq1,hq2]
      simp [Values,Nat.card_eq_fintype_card]
    have he := productOn_mono (extra designated (firstRead s c) (fun i => s.first i < t)) designated τ hτ
      (fun i hi => hi.1)
    have h := original_cut_bound φ G hφ s designated hordinary c t ht
      (fun i hi => (hsecond i).mpr hi) (fun i _ hi => hfirst i hi)
      1 (productOn designated τ) hq (by norm_num) he
    simpa using h
  · obtain ⟨t,ht,hsecond,hfirst,he⟩ := weighted_geometry s designated τ ho hτ c
    have hq : (Nat.card (Values X Y
        (fun i => designated i ∧ firstRead s c i ∧ ¬s.first i < t)
        (fun i => designated i ∧ secondRead s c i ∧ ¬s.second i < t)) : ℝ) ≤ designatedSize (X:=X) (Y:=Y) designated := by
      exact_mod_cast group_card_le_designated (X:=X) (Y:=Y) designated
        (firstRead s c) (secondRead s c) (fun i => s.first i < t) (fun i => s.second i < t)
    exact original_cut_bound φ G hφ s designated hordinary c t ht hsecond hfirst
      (designatedSize (X:=X) (Y:=Y) designated) (theta s designated τ ho) hq (Nat.cast_nonneg _) he

/-- The literal minimum of coefficient-one T and D-weighted Theta upper bounds.
All normalized layers, including initial/terminal and half pairs, are present. -/
theorem completion_width_minimum (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O)
    (hφ : ∀ i z,∃ x y,φ i x y=z) (s : Skeleton I) (designated : I → Prop)
    (ho : ∃ i,¬designated i)
    (hordinary : ∀ i,¬designated i → (∃ a:X i,Function.Surjective (φ i a)) ∧ (∃ b:Y i,Function.Surjective (fun a => φ i a b))) :
    let τ:=actualTau φ hφ
    let W:=(width φ G s.position : ℝ)
    (width φ G s.completion : ℝ) ≤ min (W^(productOn designated τ))
      (((∏ i : {i // designated i}, Fintype.card (X i.val)*Fintype.card (Y i.val) : ℕ) : ℝ) *
        W^(theta s designated τ ho)) := by
  classical
  apply width_le_of_layers
  intro t ht
  obtain ⟨c,hc⟩ := completion_all_layers s t ht
  obtain ⟨_,h1,h2⟩ := completion_prefix s c
  have he1 : (fun i => (s.completion (i,false)).val < t)=firstRead s c := by
    funext i; apply propext; simpa only [hc] using h1 i
  have he2 : (fun i => (s.completion (i,true)).val < t)=secondRead s c := by
    funext i; apply propext; simpa only [hc] using h2 i
  rw [he1,he2]
  have h := every_normalized_cut_bounds φ G hφ s designated ho hordinary c
  have hD := designated_size_formula (X:=X) (Y:=Y) designated
  exact le_min h.1 (by simpa only [hD] using h.2)

/-- Original definition of width, directly in the labelled endpoint assignment space. -/
noncomputable def labelledWidth (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O)
    (p : Endpoint I ≃ Fin (2*Fintype.card I)) : ℕ := by
  classical
  exact (Finset.range (2*Fintype.card I+1)).sup (fun t =>
    Nat.card (Set.range (labelledResponse φ G (fun v => (p v).val < t))))

private theorem labelled_width_eq (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O)
    (p : Endpoint I ≃ Fin (2*Fintype.card I)) : labelledWidth φ G p=width φ G p := by
  classical
  simp only [labelledWidth,width,labelled_response_card,cutCard]

private theorem full_task_image (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O) :
    Set.range (labelledTask φ G)=Set.range (fun b : Values X Y (fun _ => True) (fun _ => True) =>
      G (fun i => φ i (b.1 ⟨i,trivial⟩) (b.2 ⟨i,trivial⟩))) := by
  ext o
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨(fun i => a (i.val,false),fun i => a (i.val,true)),rfl⟩
  · rintro ⟨b,rfl⟩
    refine ⟨(fun v => match v with
      | (i,false) => b.1 ⟨i,trivial⟩
      | (i,true) => b.2 ⟨i,trivial⟩),rfl⟩

/-- Original labelled widths and boundary interpretation, with the literal minimum.
The final fields retain constant layers, the exact normalized cut family and response transport.
Sharpness and the least-uniform-exponent lower bound remain separate obligations. -/
theorem original_labelled_upper_contract
    (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O)
    (hφ : ∀ i z,∃ x y,φ i x y=z) (s : Skeleton I) (designated : I → Prop)
    (ho : ∃ i,¬designated i)
    (hordinary : ∀ i,¬designated i → (∃ a:X i,Function.Surjective (φ i a)) ∧ (∃ b:Y i,Function.Surjective (fun a => φ i a b))) :
    let τ:=actualTau φ hφ
    let W:=(labelledWidth φ G s.position : ℝ)
    (labelledWidth φ G s.completion : ℝ) ≤ min (W^(productOn designated τ))
      ((((∏ i : {i // designated i}, Fintype.card (X i.val)*Fintype.card (Y i.val) : ℕ) : ℝ)) *
        W^(theta s designated τ ho)) ∧
    Nat.card (Set.range (labelledResponse φ G (fun _ => False)))=1 ∧
    Nat.card (Set.range (labelledResponse φ G (fun _ => True)))=Nat.card (Set.range (labelledTask φ G)) ∧
    (∀ (o : O) (C : Endpoint I → Prop), Nat.card (Set.range (labelledResponse φ (fun _ => o) C))=1) ∧
    (∀ l r : I → Prop,
      (∃ t ≤ 2*Fintype.card I,
        (∀ i,l i↔(s.completion (i,false)).val < t) ∧ (∀ i,r i↔(s.completion (i,true)).val < t)) ↔
      ∃ c : Cut I,(∀ i,l i↔firstRead s c i) ∧ (∀ i,r i↔secondRead s c i)) ∧
    (∀ c : Cut I,
      Nat.card (Set.range (labelledResponse φ G (fun v => (s.completion v).val < cutSize s c)))=
        cutCard φ G (firstRead s c) (secondRead s c)) := by
  classical
  refine ⟨?_,?_,?_,?_,completion_cut_family s,normalized_card_transport φ G s⟩
  · simpa only [labelled_width_eq] using completion_width_minimum φ G hφ s designated ho hordinary
  · rw [labelled_response_card]
    exact (initial_and_constant_layers φ G).1
  · rw [labelled_response_card,full_task_image φ G]
    exact terminal_layer φ G
  · intro o C
    rw [labelled_response_card]
    exact (initial_and_constant_layers φ G).2 o _ _

end CompletionSorting

section WeightedBooleanSharpness

variable {A B Z : Type} [Fintype A] [Fintype B] [Fintype Z]
  [Nonempty A] [Nonempty B]

/-- Actual row membership, with the same complete selector suffix. -/
abbrev Row (φ : A → B → Z) (a : A) := {z // ∃ b, φ a b=z}
abbrev PositiveRow (φ : A → B → Z) (ell : Z → ℕ) (a : A) := {z : Row φ a // 0 < ell z.val}
abbrev Cell (m : ℕ) (ell : Z → ℕ) (z : Z) := ZMod (m^ell z)
abbrev Table (m : ℕ) (ell : Z → ℕ) := ∀ z,Cell m ell z

instance cellNeZero (m : ℕ) [NeZero m] (ell : Z → ℕ) (z : Z) : NeZero (m^ell z) :=
  ⟨pow_ne_zero _ (NeZero.ne m)⟩

noncomputable def zeroTest (φ : A → B → Z) (m : ℕ) (ell : Z → ℕ)
    (a b : Table m ell) (x : A) (y : B) : Bool := by
  classical
  exact decide (a (φ x y)+b (φ x y)=0)

/-- An exact common denominator from the pinned matrix-integer supplier.
No rationality or integer weight is supplied by the caller. -/
theorem integer_optimal_certificate (φ : A → B → Z) (hφ : ∀ z,∃ x y,φ x y=z) :
    ∃ (L : ℕ) (ell : Z → ℕ), 0 < L ∧
      ((∑ z,ell z : ℕ):ℝ)=(L:ℝ)*rowCoverNumber φ hφ ∧
      (∀ x, (∑ z : Row φ x,ell z.val) ≤ L) := by
  classical
  obtain ⟨w,hlam,hcover,hw,hrows,heq,_,_⟩ := optimal_row_cover_spec φ hφ
  let M : Matrix Z Unit ℚ := fun z _ => w z
  let L := M.den
  have hL : 0 < L := Nat.pos_of_ne_zero M.den_ne_zero
  have hden : (L:ℚ)≠0 := by exact_mod_cast hL.ne'
  have hnum (z : Z) : (M.num z () : ℚ)=(L:ℚ)*w z := by
    have h := (div_eq_iff hden).mp (M.num_div_den z ())
    simpa [M,L,mul_comm] using h
  have hn (z : Z) : 0 ≤ M.num z () := by
    have hwz := hw z
    have h : (0:ℚ) ≤ (M.num z () : ℚ) := by rw [hnum]; positivity
    exact_mod_cast h
  let ell : Z → ℕ := fun z => (M.num z ()).toNat
  have hell (z : Z) : (ell z : ℚ)=(L:ℚ)*w z := by
    have hc : ((ell z : ℕ):ℤ)=M.num z () := Int.toNat_of_nonneg (hn z)
    have hq : (ell z : ℚ)=(M.num z () : ℚ) := by exact_mod_cast hc
    exact hq.trans (hnum z)
  have htotal : ((∑ z,ell z : ℕ):ℚ)=(L:ℚ)*∑ z,w z := by
    rw [Nat.cast_sum,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z _ => hell z)
  have hopt : ((∑ z,w z : ℚ):ℝ)=rowCoverNumber φ hφ := by
    rw [←heq,Rat.cast_sum]
    rfl
  refine ⟨L,ell,hL,?_,?_⟩
  · have hh : ((∑ z,ell z : ℕ):ℝ)=(L:ℝ)*((∑ z,w z : ℚ):ℝ) := by exact_mod_cast htotal
    rwa [hopt] at hh
  · intro x
    have hs : (∑ z : Row φ x,w z.val)=∑ z,if (∃ y,φ x y=z) then w z else 0 := by
      rw [←Finset.sum_filter]
      exact (Finset.sum_subtype (p := fun z => ∃ y,φ x y=z) (Finset.univ.filter (fun z => ∃ y,φ x y=z))
        (by intro z; simp [Row]) w).symm
    have hb : (∑ z : Row φ x,w z.val) ≤ 1 := by
      rw [hs]
      convert hrows x using 1
      apply Finset.sum_congr rfl
      intro z _
      by_cases h : ∃ y,φ x y=z <;> simp [h]
    have hscale : ((∑ z : Row φ x,ell z.val : ℕ):ℚ)=
        (L:ℚ)*∑ z : Row φ x,w z.val := by
      rw [Nat.cast_sum,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun z _ => hell z.val)
    have hq : ((∑ z : Row φ x,ell z.val : ℕ):ℚ) ≤ L := by
      rw [hscale]
      simpa using mul_le_mul_of_nonneg_left hb (by positivity : (0:ℚ) ≤ L)
    exact_mod_cast hq

private theorem table_card (m : ℕ) [NeZero m] (ell : Z → ℕ) :
    Nat.card (Table m ell)=m^(∑ z,ell z) := by
  classical
  simp only [Nat.card_eq_fintype_card,Fintype.card_pi,ZMod.card]
  exact Finset.prod_pow_eq_pow_sum Finset.univ ell m

private theorem row_table_card (φ : A → B → Z) (m : ℕ) [NeZero m] (ell : Z → ℕ) (x : A) :
    Nat.card (∀ z : Row φ x,Cell m ell z.val)=m^(∑ z : Row φ x,ell z.val) := by
  classical
  simp only [Nat.card_eq_fintype_card,Fintype.card_pi,ZMod.card]
  exact Finset.prod_pow_eq_pow_sum Finset.univ (fun z : Row φ x => ell z.val) m

/-- Only positive-weight coordinates can supply nonconstant zero flags. -/
private theorem positive_row_card (φ : A → B → Z) (ell : Z → ℕ) (x : A) :
    Nat.card (PositiveRow φ ell x) ≤ ∑ z : Row φ x,ell z.val := by
  classical
  let f : PositiveRow φ ell x → Σ z : Row φ x,Fin (ell z.val) :=
    fun z => ⟨z.val,⟨0,z.property⟩⟩
  have hf : Function.Injective f := by
    intro z z' h
    exact Subtype.ext (congrArg Sigma.fst h)
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_fin] using h

private theorem zero_weight_value (m : ℕ) (ell : Z → ℕ) (z : Z) (hz : ell z=0)
    (v : Cell m ell z) : v=0 := by
  have hmod : m^ell z=1 := by simp [hz]
  haveI : Subsingleton (ZMod (m^ell z)) := ZMod.subsingleton_iff.mpr hmod
  exact Subsingleton.elim _ _

/-- Signature of a real half-read addition prefix, tagged by its actual x. -/
abbrev MiddleSignature (φ : A → B → Z) (m : ℕ) (ell : Z → ℕ) :=
  Σ x : A,∀ z : Row φ x,Cell m ell z.val

noncomputable def middleSignature (φ : A → B → Z) (m : ℕ) (ell : Z → ℕ)
    (x : A) (a : Table m ell) : MiddleSignature φ m ell :=
  ⟨x,fun z => a z.val⟩

noncomputable def middleDecode (φ : A → B → Z) (m : ℕ) (ell : Z → ℕ)
    (v : MiddleSignature φ m ell) (b : Table m ell) (y : B) : Bool := by
  classical
  exact decide (v.2 ⟨φ v.1 y,⟨y,rfl⟩⟩+b (φ v.1 y)=0)

/-- Signature after addition has completed: raw observed y information is retained
by the caller's actual partial-coordinate extension; only positive row flags vary. -/
abbrev AfterSignature (φ : A → B → Z) (ell : Z → ℕ) :=
  Σ x : A,B × (PositiveRow φ ell x → Bool)

noncomputable def afterSignature (φ : A → B → Z) (m : ℕ) (ell : Z → ℕ)
    (x : A) (observedY : B) (a b : Table m ell) : AfterSignature φ ell := by
  classical
  exact ⟨x,observedY,fun z => decide (a z.val.val+b z.val.val=0)⟩

noncomputable def afterDecode (φ : A → B → Z) (ell : Z → ℕ)
    (v : AfterSignature φ ell) (joinY : B → B → B) (unreadY : B) : Bool := by
  classical
  let y := joinY v.2.1 unreadY
  let z : Row φ v.1 := ⟨φ v.1 y,⟨y,rfl⟩⟩
  exact if h : 0 < ell z.val then v.2.2 ⟨z,h⟩ else true

private theorem after_decode_actual (φ : A → B → Z) (m : ℕ) (ell : Z → ℕ)
    (x : A) (yp yq : B) (a b : Table m ell) (joinY : B → B → B) :
    afterDecode φ ell (afterSignature φ m ell x yp a b) joinY yq=
      zeroTest φ m ell a b x (joinY yp yq) := by
  classical
  let z := φ x (joinY yp yq)
  by_cases h : 0 < ell z
  · simp [afterDecode,afterSignature,zeroTest,z,h]
  · have hz : ell z=0 := by omega
    have ha := zero_weight_value m ell z hz (a z)
    have hb := zero_weight_value m ell z hz (b z)
    simp [afterDecode,afterSignature,zeroTest,z,h,ha,hb]

private theorem middle_signature_card_bound (φ : A → B → Z) (m L : ℕ) [NeZero m]
    (hm : 1 ≤ m) (ell : Z → ℕ) (hrow : ∀ x,(∑ z : Row φ x,ell z.val) ≤ L) :
    Nat.card (MiddleSignature φ m ell) ≤ Nat.card A*m^L := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  have h : (∑ x, Nat.card (∀ z : Row φ x,Cell m ell z.val)) ≤ ∑ _x : A,m^L := by
    apply Finset.sum_le_sum
    intro x _
    rw [row_table_card]
    exact Nat.pow_le_pow_right hm (hrow x)
  simpa only [Nat.card_eq_fintype_card,Finset.sum_const,Finset.card_univ,smul_eq_mul] using h

private theorem after_signature_card_bound (φ : A → B → Z) (m L : ℕ)
    (hm : 2 ≤ m) (ell : Z → ℕ) (hrow : ∀ x,(∑ z : Row φ x,ell z.val) ≤ L) :
    Nat.card (AfterSignature φ ell) ≤ Nat.card A*Nat.card B*m^L := by
  classical
  have hpos : ∀ x,Nat.card (PositiveRow φ ell x) ≤ L :=
    fun x => (positive_row_card φ ell x).trans (hrow x)
  have hflags : ∀ x,Nat.card (PositiveRow φ ell x → Bool) ≤ m^L := by
    intro x
    rw [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_bool]
    exact (Nat.pow_le_pow_right (by omega) (by simpa only [Nat.card_eq_fintype_card] using hpos x)).trans
      (Nat.pow_le_pow_left hm L)
  have hsum : (∑ x, Nat.card B*Nat.card (PositiveRow φ ell x → Bool)) ≤ ∑ _x : A,Nat.card B*m^L := by
    exact Finset.sum_le_sum (fun x _ => Nat.mul_le_mul_left _ (hflags x))
  simpa [AfterSignature,Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_prod,mul_assoc] using hsum

end WeightedBooleanSharpness

section WeightedBooleanSharpness

variable {R S : Type} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
  {X Y Z : R → Type} [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)] [∀ i,Fintype (Z i)]
  [∀ i,Nonempty (X i)] [∀ i,Nonempty (Y i)]

/-- The exact original strict containment neighborhood of an ordinary pair. -/
def N (s : Skeleton (R ⊕ S)) (k : S) (i : R) : Prop :=
  s.first (.inl i) < s.first (.inr k) ∧ s.first (.inr k) < s.second (.inr k) ∧
    s.second (.inr k) < s.second (.inl i)

abbrev XP (s : Skeleton (R ⊕ S)) (k : S) := ∀ i : {i // N s k i},X i.val
abbrev YP (s : Skeleton (R ⊕ S)) (k : S) := ∀ i : {i // N s k i},Y i.val
abbrev ZP (s : Skeleton (R ⊕ S)) (k : S) := ∀ i : {i // N s k i},Z i.val

def productMap (s : Skeleton (R ⊕ S)) (k : S) (φ : ∀ i,X i → Y i → Z i) :
    XP (X:=X) s k → YP (Y:=Y) s k → ZP (Z:=Z) s k := fun x y i => φ i.val (x i) (y i)

private theorem productMap_onto (s : Skeleton (R ⊕ S)) (k : S)
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z) :
    ∀ z,∃ x y,productMap s k φ x y=z := by
  intro z
  choose x y h using fun i : {i // N s k i} => hφ i.val (z i)
  exact ⟨x,y,funext h⟩

/-- Only k has a changing alphabet. Every other ordinary alphabet is Bool. -/
noncomputable def FamilyX (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ) : R ⊕ S → Type _
  | .inl i => X i
  | .inr j => if j=k then Table m ell else Bool
noncomputable def FamilyY (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ) : R ⊕ S → Type _
  | .inl i => Y i
  | .inr j => if j=k then Table m ell else Bool
noncomputable def FamilyZ (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ) : R ⊕ S → Type _
  | .inl i => Z i
  | .inr j => if j=k then Table m ell else Bool

noncomputable instance familyXFintype (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) [NeZero m] (ell : ZP (Z:=Z) s k → ℕ)
    (i : R ⊕ S) : Fintype (FamilyX (X:=X) s k m ell i) := by
  classical
  cases i with
  | inl i => exact inferInstanceAs (Fintype (X i))
  | inr j => by_cases h:j=k <;> simp only [FamilyX,h,ite_true,ite_false] <;> infer_instance
noncomputable instance familyYFintype (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) [NeZero m] (ell : ZP (Z:=Z) s k → ℕ)
    (i : R ⊕ S) : Fintype (FamilyY (Y:=Y) s k m ell i) := by
  classical
  cases i with
  | inl i => exact inferInstanceAs (Fintype (Y i))
  | inr j => by_cases h:j=k <;> simp only [FamilyY,h,ite_true,ite_false] <;> infer_instance
noncomputable instance familyZFintype (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) [NeZero m] (ell : ZP (Z:=Z) s k → ℕ)
    (i : R ⊕ S) : Fintype (FamilyZ (Z:=Z) s k m ell i) := by
  classical
  cases i with
  | inl i => exact inferInstanceAs (Fintype (Z i))
  | inr j => by_cases h:j=k <;> simp only [FamilyZ,h,ite_true,ite_false] <;> infer_instance
noncomputable instance familyXNonempty (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ)
    (i : R ⊕ S) : Nonempty (FamilyX (X:=X) s k m ell i) := by
  classical
  cases i with
  | inl i => exact inferInstanceAs (Nonempty (X i))
  | inr j => by_cases h:j=k <;> simp only [FamilyX,h,ite_true,ite_false] <;> infer_instance
noncomputable instance familyYNonempty (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ)
    (i : R ⊕ S) : Nonempty (FamilyY (Y:=Y) s k m ell i) := by
  classical
  cases i with
  | inl i => exact inferInstanceAs (Nonempty (Y i))
  | inr j => by_cases h:j=k <;> simp only [FamilyY,h,ite_true,ite_false] <;> infer_instance

/- These equivalences are the only type transports at ordinary coordinates.
Their inverse maps construct actual endpoint values in the original alphabets. -/
noncomputable def selectedX (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (j : S) (h : j=k) :
    FamilyX (X:=X) s k m ell (.inr j) ≃ Table m ell := by
  classical
  exact Equiv.cast (by simp only [FamilyX,if_pos h])
noncomputable def selectedY (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (j : S) (h : j=k) :
    FamilyY (Y:=Y) s k m ell (.inr j) ≃ Table m ell := by
  classical
  exact Equiv.cast (by simp only [FamilyY,if_pos h])
noncomputable def selectedZ (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (j : S) (h : j=k) :
    FamilyZ (Z:=Z) s k m ell (.inr j) ≃ Table m ell := by
  classical
  exact Equiv.cast (by simp only [FamilyZ,if_pos h])
noncomputable def otherX (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (j : S) (h : j≠k) :
    FamilyX (X:=X) s k m ell (.inr j) ≃ Bool := by
  classical
  exact Equiv.cast (by simp only [FamilyX,if_neg h])
noncomputable def otherY (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (j : S) (h : j≠k) :
    FamilyY (Y:=Y) s k m ell (.inr j) ≃ Bool := by
  classical
  exact Equiv.cast (by simp only [FamilyY,if_neg h])
noncomputable def otherZ (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (j : S) (h : j≠k) :
    FamilyZ (Z:=Z) s k m ell (.inr j) ≃ Bool := by
  classical
  exact Equiv.cast (by simp only [FamilyZ,if_neg h])

private def transportBinary {A : Type} {B : Type} {C : Type} {A' : Type} {B' : Type} {C' : Type}
    (ea : A ≃ A') (eb : B ≃ B') (ec : C ≃ C')
    (f : A' → B' → C') (a : A) (b : B) : C :=
  ec.symm (f (ea a) (eb b))

private theorem transportBinary_decode {A : Type} {B : Type} {C : Type} {A' : Type} {B' : Type} {C' : Type}
    (ea : A ≃ A') (eb : B ≃ B') (ec : C ≃ C')
    (f : A' → B' → C') (a : A) (b : B) :
    ec (transportBinary ea eb ec f a b)=f (ea a) (eb b) :=
  ec.apply_symm_apply _

/-- Surjective slices survive independent equivalences of the three alphabets. -/
private theorem transportBinary_slices {A : Type} {B : Type} {C : Type} {A' : Type} {B' : Type} {C' : Type}
    (ea : A ≃ A') (eb : B ≃ B') (ec : C ≃ C') (f : A' → B' → C')
    (hf : (∃ a,Function.Surjective (f a)) ∧
      (∃ b,Function.Surjective (fun a => f a b))) :
    (∃ a,Function.Surjective (transportBinary ea eb ec f a)) ∧
      (∃ b,Function.Surjective (fun a => transportBinary ea eb ec f a b)) := by
  rcases hf with ⟨⟨a,ha⟩,⟨b,hb⟩⟩
  constructor
  · refine ⟨ea.symm a,?_⟩
    intro z
    obtain ⟨y,hy⟩ := ha (ec z)
    refine ⟨eb.symm y,?_⟩
    apply ec.injective
    rw [transportBinary_decode]
    simpa only [Equiv.apply_symm_apply] using hy
  · refine ⟨eb.symm b,?_⟩
    intro z
    obtain ⟨x,hx⟩ := hb (ec z)
    refine ⟨ea.symm x,?_⟩
    apply ec.injective
    rw [transportBinary_decode]
    simpa only [Equiv.apply_symm_apply] using hx

noncomputable def familyMap (s : Skeleton (R ⊕ S)) (k : S) (φ : ∀ i,X i → Y i → Z i)
    (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ) :
    ∀ i,FamilyX (X:=X) s k m ell i → FamilyY (Y:=Y) s k m ell i → FamilyZ s k m ell i
  | .inl i => φ i
  | .inr j => by
    classical
    exact if h:j=k then
      transportBinary (selectedX (X:=X) s k m ell j h) (selectedY (Y:=Y) s k m ell j h)
        (selectedZ (Z:=Z) s k m ell j h) (fun a b : Table m ell => a+b)
    else
      transportBinary (otherX (X:=X) s k m ell j h) (otherY (Y:=Y) s k m ell j h)
        (otherZ (Z:=Z) s k m ell j h) Bool.xor

/-- Typed projection onto the designated selector tuple. -/
def designatedTuple (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (v : ∀ i,FamilyZ s k m ell i) : ZP (Z:=Z) s k :=
  fun i => v (.inl i.val)

/-- Typed projection onto the changing ordinary output. -/
noncomputable def selectedTable (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (v : ∀ i,FamilyZ s k m ell i) : Table m ell :=
  selectedZ (Z:=Z) s k m ell k rfl (v (.inr k))

noncomputable def familyOuter (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (v : ∀ i,FamilyZ s k m ell i) : Bool := by
  classical
  exact decide ((selectedTable s k m ell v) (designatedTuple s k m ell v)=0)

private theorem familyMap_selected_decode (s : Skeleton (R ⊕ S)) (k : S)
    (φ : ∀ i,X i → Y i → Z i) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ)
    (a : FamilyX (X:=X) s k m ell (.inr k))
    (b : FamilyY (Y:=Y) s k m ell (.inr k)) :
    selectedZ (Z:=Z) s k m ell k rfl (familyMap s k φ m ell (.inr k) a b)=
      selectedX (X:=X) s k m ell k rfl a + selectedY (Y:=Y) s k m ell k rfl b := by
  classical
  simp [familyMap,transportBinary]

def FamilyAllowed (s : Skeleton (R ⊕ S)) (k : S) (φ : ∀ i,X i → Y i → Z i)
    (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ) : Prop :=
    (∀ i,familyMap s k φ m ell (.inl i)=φ i) ∧
    (∀ j,
      (∃ a,Function.Surjective (familyMap s k φ m ell (.inr j) a)) ∧
      (∃ b,Function.Surjective (fun a => familyMap s k φ m ell (.inr j) a b))) ∧
    (∀ i z,∃ x y,familyMap s k φ m ell i x y=z)

/-- Actual surjective slices in the original conditional alphabets. -/
theorem family_allowed (s : Skeleton (R ⊕ S)) (k : S) (φ : ∀ i,X i → Y i → Z i)
    (hφ : ∀ i z,∃ x y,φ i x y=z) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ) :
    FamilyAllowed s k φ m ell := by
  classical
  have ordinary (j : S) :
      (∃ a,Function.Surjective (familyMap s k φ m ell (.inr j) a)) ∧
      (∃ b,Function.Surjective (fun a => familyMap s k φ m ell (.inr j) a b)) := by
    by_cases h:j=k
    · simp only [familyMap,dif_pos h]
      apply transportBinary_slices
      exact ⟨⟨0,fun z => ⟨z,zero_add z⟩⟩,⟨0,fun z => ⟨z,add_zero z⟩⟩⟩
    · simp only [familyMap,dif_neg h]
      apply transportBinary_slices
      exact ⟨⟨false,fun z => ⟨z,by cases z <;> rfl⟩⟩,
        ⟨false,fun z => ⟨z,by cases z <;> rfl⟩⟩⟩
  refine ⟨fun i => rfl,ordinary,?_⟩
  intro i z
  cases i with
  | inl i => exact hφ i z
  | inr j => obtain ⟨a,ha⟩ := (ordinary j).1; obtain ⟨b,hb⟩ := ha z; exact ⟨a,b,hb⟩

section RawReadouts
variable (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ)

abbrev Prefix (l r : R ⊕ S → Prop) := Values (FamilyX (X:=X) s k m ell) (FamilyY (Y:=Y) s k m ell) l r
abbrev Suffix (l r : R ⊕ S → Prop) := Prefix (X:=X) (Y:=Y) s k m ell (fun i=>¬l i) (fun i=>¬r i)

noncomputable def preX (l r : R ⊕ S → Prop) (b : Prefix (X:=X) (Y:=Y) s k m ell l r) : XP (X:=X) s k := by
  classical
  exact fun i => if h:l (.inl i.val) then b.1 ⟨.inl i.val,h⟩ else Classical.choice inferInstance
noncomputable def sufX (l r : R ⊕ S → Prop) (q : Suffix (X:=X) (Y:=Y) s k m ell l r) : XP (X:=X) s k := by
  classical
  exact fun i => if h:¬l (.inl i.val) then q.1 ⟨.inl i.val,h⟩ else Classical.choice inferInstance
noncomputable def preY (l r : R ⊕ S → Prop) (b : Prefix (X:=X) (Y:=Y) s k m ell l r) : YP (Y:=Y) s k := by
  classical
  exact fun i => if h:r (.inl i.val) then b.2 ⟨.inl i.val,h⟩ else Classical.choice inferInstance
noncomputable def sufY (l r : R ⊕ S → Prop) (q : Suffix (X:=X) (Y:=Y) s k m ell l r) : YP (Y:=Y) s k := by
  classical
  exact fun i => if h:¬r (.inl i.val) then q.2 ⟨.inl i.val,h⟩ else Classical.choice inferInstance
noncomputable def joinX (l : R ⊕ S → Prop) (x x' : XP (X:=X) s k) : XP (X:=X) s k := by
  classical
  exact fun i => if l (.inl i.val) then x i else x' i
noncomputable def joinY (r : R ⊕ S → Prop) (y y' : YP (Y:=Y) s k) : YP (Y:=Y) s k := by
  classical
  exact fun i => if r (.inl i.val) then y i else y' i

noncomputable def preA (l r : R ⊕ S → Prop) (b : Prefix (X:=X) (Y:=Y) s k m ell l r) : Table m ell := by
  classical
  exact if h:l (.inr k) then selectedX (X:=X) s k m ell k rfl (b.1 ⟨.inr k,h⟩) else 0
noncomputable def sufA (l r : R ⊕ S → Prop) (q : Suffix (X:=X) (Y:=Y) s k m ell l r) : Table m ell := by
  classical
  exact if h:¬l (.inr k) then selectedX (X:=X) s k m ell k rfl (q.1 ⟨.inr k,h⟩) else 0
noncomputable def preB (l r : R ⊕ S → Prop) (b : Prefix (X:=X) (Y:=Y) s k m ell l r) : Table m ell := by
  classical
  exact if h:r (.inr k) then selectedY (Y:=Y) s k m ell k rfl (b.2 ⟨.inr k,h⟩) else 0
noncomputable def sufB (l r : R ⊕ S → Prop) (q : Suffix (X:=X) (Y:=Y) s k m ell l r) : Table m ell := by
  classical
  exact if h:¬r (.inr k) then selectedY (Y:=Y) s k m ell k rfl (q.2 ⟨.inr k,h⟩) else 0

/-- The partitioned endpoint is decoded once, with its other summand zero. -/
private theorem decode_partitioned_coordinate {I : Type} {A : Type} {V : I → Type}
    [AddMonoid A] (p : I → Prop) [DecidablePred p] (i : I) (e : V i ≃ A)
    (b : ∀ j : {j // p j},V j.val) (q : ∀ j : {j // ¬p j},V j.val) :
    e (if h:p i then b ⟨i,h⟩ else q ⟨i,h⟩)=
      (if h:p i then e (b ⟨i,h⟩) else 0) +
      (if h:¬p i then e (q ⟨i,h⟩) else 0) := by
  by_cases h:p i <;> simp [h]

/-- Equality of entire dependent selector tuples, before table evaluation. -/
private theorem designatedTuple_outputs (φ : ∀ i,X i → Y i → Z i) (l r : R ⊕ S → Prop)
    (b : Prefix (X:=X) (Y:=Y) s k m ell l r)
    (q : Suffix (X:=X) (Y:=Y) s k m ell l r) :
    designatedTuple s k m ell (outputs (familyMap s k φ m ell) l r b q)=
      productMap s k φ
        (joinX s k l (preX s k m ell l r b) (sufX s k m ell l r q))
        (joinY s k r (preY s k m ell l r b) (sufY s k m ell l r q)) := by
  classical
  funext i
  change φ i.val
      (if h:l (.inl i.val) then b.1 ⟨.inl i.val,h⟩ else q.1 ⟨.inl i.val,h⟩)
      (if h:r (.inl i.val) then b.2 ⟨.inl i.val,h⟩ else q.2 ⟨.inl i.val,h⟩)=
    φ i.val
      (joinX s k l (preX s k m ell l r b) (sufX s k m ell l r q) i)
      (joinY s k r (preY s k m ell l r b) (sufY s k m ell l r q) i)
  apply congrArg₂ (φ i.val)
  · by_cases h:l (.inl i.val) <;> simp [joinX,preX,sufX,h] <;> rfl
  · by_cases h:r (.inl i.val) <;> simp [joinY,preY,sufY,h] <;> rfl

/-- Equality of whole tables; the changing ordinary map is actual addition. -/
private theorem selectedTable_outputs (φ : ∀ i,X i → Y i → Z i) (l r : R ⊕ S → Prop)
    (b : Prefix (X:=X) (Y:=Y) s k m ell l r)
    (q : Suffix (X:=X) (Y:=Y) s k m ell l r) :
    selectedTable s k m ell (outputs (familyMap s k φ m ell) l r b q)=
      (preA s k m ell l r b+sufA s k m ell l r q)+
      (preB s k m ell l r b+sufB s k m ell l r q) := by
  classical
  change selectedZ (Z:=Z) s k m ell k rfl
    (familyMap s k φ m ell (.inr k)
      (if h:l (.inr k) then b.1 ⟨.inr k,h⟩ else q.1 ⟨.inr k,h⟩)
      (if h:r (.inr k) then b.2 ⟨.inr k,h⟩ else q.2 ⟨.inr k,h⟩))=_
  rw [familyMap_selected_decode]
  apply congrArg₂ (fun a b : Table m ell => a+b)
  · simpa only [preA,sufA] using
      decode_partitioned_coordinate l (.inr k) (selectedX (X:=X) s k m ell k rfl) b.1 q.1
  · simpa only [preB,sufB] using
      decode_partitioned_coordinate r (.inr k) (selectedY (Y:=Y) s k m ell k rfl) b.2 q.2

/-- Evaluation of the actual full task on this one original labelled suffix. -/
theorem sharp_response_formula (φ : ∀ i,X i → Y i → Z i) (l r : R ⊕ S → Prop)
    (b : Prefix (X:=X) (Y:=Y) s k m ell l r) (q : Suffix (X:=X) (Y:=Y) s k m ell l r) :
    response (familyMap s k φ m ell) (familyOuter s k m ell) l r b q=
      zeroTest (productMap s k φ) m ell
        (preA s k m ell l r b+sufA s k m ell l r q)
        (preB s k m ell l r b+sufB s k m ell l r q)
        (joinX s k l (preX s k m ell l r b) (sufX s k m ell l r q))
        (joinY s k r (preY s k m ell l r b) (sufY s k m ell l r q)) := by
  classical
  change decide
    ((selectedTable s k m ell (outputs (familyMap s k φ m ell) l r b q))
      (designatedTuple s k m ell (outputs (familyMap s k φ m ell) l r b q))=0)=_
  rw [selectedTable_outputs,designatedTuple_outputs]
  rfl

end RawReadouts

private theorem response_le_signature {P Q V : Type} [Finite P] [Finite Q] [Finite V]
    (responseMap : P → Q) (signature : P → V)
    (h : ∀ p p',signature p=signature p' → responseMap p=responseMap p') :
    Nat.card (Set.range responseMap) ≤ Nat.card V :=
  (range_card_le_of_kernel signature responseMap h).trans
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

set_option maxHeartbeats 1600000 in
/-- The three regimes cover every original endpoint layer, including interleaved
ignored coordinates, partial designated Y prefixes and the final layer. -/
theorem raw_layer_signature_bounds (s : Skeleton (R ⊕ S)) (k : S)
    (φ : ∀ i,X i → Y i → Z i) (m L : ℕ) [NeZero m] (hm : 2 ≤ m) (ell : ZP (Z:=Z) s k → ℕ)
    (hrow : ∀ x,(∑ z : Row (productMap s k φ) x,ell z.val) ≤ L) (t : ℕ) :
    let l := fun i => s.first i < t
    let r := fun i => s.second i < t
    let cap := cutCard (familyMap s k φ m ell) (familyOuter s k m ell) l r
    (t ≤ s.first (.inr k) → cap ≤ Nat.card (XP (X:=X) s k)) ∧
    (s.first (.inr k) < t → t ≤ s.second (.inr k) → cap ≤ Nat.card (XP (X:=X) s k)*m^L) ∧
    (s.second (.inr k) < t → cap ≤ Nat.card (XP (X:=X) s k)*Nat.card (YP (Y:=Y) s k)*m^L) := by
  let l := fun i => s.first i < t
  let r := fun i => s.second i < t
  let f := response (familyMap s k φ m ell) (familyOuter s k m ell) l r
  have hk := s.oriented (.inr k)
  change s.first (.inr k) < s.second (.inr k) at hk
  refine ⟨?_,?_,?_⟩
  · intro ht
    have ha : ¬l (.inr k) := by dsimp [l]; omega
    have hb : ¬r (.inr k) := by dsimp [r]; omega
    have hy : ∀ i : {i // N s k i},¬r (.inl i.val) := by
      intro i; have h:=i.property.2.2; dsimp [r]; omega
    apply response_le_signature f (preX s k m ell l r)
    intro b b' he
    funext q
    have hyjoin (b : Prefix (X:=X) (Y:=Y) s k m ell l r) : joinY s k r (preY s k m ell l r b) (sufY s k m ell l r q)=
        sufY s k m ell l r q := by funext i; simp [joinY,hy i]
    dsimp only [f]
    rw [sharp_response_formula,sharp_response_formula,hyjoin,hyjoin]
    simp [preA,preB,ha,hb,he]
  · intro hta htb
    have ha : l (.inr k) := hta
    have hb : ¬r (.inr k) := by dsimp [r]; omega
    have hx : ∀ i : {i // N s k i},l (.inl i.val) := by
      intro i; exact lt_trans i.property.1 hta
    have hy : ∀ i : {i // N s k i},¬r (.inl i.val) := by
      intro i; have h:=i.property.2.2; dsimp [r]; omega
    let sig := fun b : Prefix (X:=X) (Y:=Y) s k m ell l r =>
      middleSignature (productMap s k φ) m ell (preX s k m ell l r b) (preA s k m ell l r b)
    have factor (b : Prefix (X:=X) (Y:=Y) s k m ell l r) (q : Suffix (X:=X) (Y:=Y) s k m ell l r) : f b q=middleDecode (productMap s k φ) m ell (sig b)
        (sufB s k m ell l r q) (sufY s k m ell l r q) := by
      have ex : joinX s k l (preX s k m ell l r b) (sufX s k m ell l r q)=preX s k m ell l r b := by
        funext i; simp [joinX,hx i]
      have ey : joinY s k r (preY s k m ell l r b) (sufY s k m ell l r q)=sufY s k m ell l r q := by
        funext i; simp [joinY,hy i]
      dsimp only [f]
      rw [sharp_response_formula,ex,ey]
      simp [sig,middleSignature,middleDecode,zeroTest,sufA,preB,ha,hb]
      congr 1
    have hbnd := response_le_signature f sig (by
      intro b b' he; funext q; rw [factor,factor,he])
    have hcard : Nat.card (MiddleSignature (productMap s k φ) m ell) ≤
        Nat.card (XP (X:=X) s k)*m^L := by
      apply middle_signature_card_bound (A:=XP (X:=X) s k) (B:=YP (Y:=Y) s k)
        (Z:=ZP (Z:=Z) s k) (productMap s k φ) m L (by omega) ell
      intro x
      apply le_trans ?_ (hrow x)
      apply le_of_eq
      apply Finset.sum_congr
      · ext z; simp
      · intro z hz; rfl
    exact Nat.le_trans hbnd hcard
  · intro htb
    have ha : l (.inr k) := lt_trans hk htb
    have hb : r (.inr k) := htb
    have hx : ∀ i : {i // N s k i},l (.inl i.val) := fun i => lt_trans i.property.1 ha
    let sig := fun b : Prefix (X:=X) (Y:=Y) s k m ell l r =>
      afterSignature (productMap s k φ) m ell (preX s k m ell l r b) (preY s k m ell l r b)
        (preA s k m ell l r b) (preB s k m ell l r b)
    have factor (b : Prefix (X:=X) (Y:=Y) s k m ell l r) (q : Suffix (X:=X) (Y:=Y) s k m ell l r) : f b q=afterDecode (productMap s k φ) ell (sig b)
        (joinY s k r) (sufY s k m ell l r q) := by
      have ex : joinX s k l (preX s k m ell l r b) (sufX s k m ell l r q)=preX s k m ell l r b := by
        funext i; simp [joinX,hx i]
      dsimp only [f]
      rw [sharp_response_formula,ex]
      rw [show sig b=afterSignature _ _ _ _ _ _ _ from rfl,after_decode_actual]
      simp [sufA,sufB,ha,hb]
    have hbnd := response_le_signature f sig (by
      intro b b' he; funext q; rw [factor,factor,he])
    have hcard : Nat.card (AfterSignature (productMap s k φ) ell) ≤
        Nat.card (XP (X:=X) s k)*Nat.card (YP (Y:=Y) s k)*m^L := by
      apply after_signature_card_bound (A:=XP (X:=X) s k) (B:=YP (Y:=Y) s k)
        (Z:=ZP (Z:=Z) s k) (productMap s k φ) m L hm ell
      intro x
      apply le_trans ?_ (hrow x)
      apply le_of_eq
      apply Finset.sum_congr
      · ext z; simp
      · intro z hz; rfl
    exact Nat.le_trans hbnd hcard

/-- Uniform original-width bound with a fixed coefficient, independent of m. -/
theorem sharp_original_width_bound (s : Skeleton (R ⊕ S)) (k : S)
    (φ : ∀ i,X i → Y i → Z i) (m L : ℕ) [NeZero m] (hm : 2 ≤ m) (ell : ZP (Z:=Z) s k → ℕ)
    (hrow : ∀ x,(∑ z : Row (productMap s k φ) x,ell z.val) ≤ L) :
    1 ≤ width (familyMap s k φ m ell) (familyOuter s k m ell) s.position ∧
    width (familyMap s k φ m ell) (familyOuter s k m ell) s.position ≤ Nat.card (XP (X:=X) s k)*Nat.card (YP (Y:=Y) s k)*m^L := by
  have hx : 1 ≤ Nat.card (XP (X:=X) s k) := Nat.card_pos
  have hy : 1 ≤ Nat.card (YP (Y:=Y) s k) := Nat.card_pos
  have hp : 1 ≤ m^L := by
    have hpositive : 0 < m^L := pow_pos (by omega : 0 < m) L
    omega
  refine ⟨width_pos _ _ _,?_⟩
  apply Finset.sup_le
  intro t ht
  obtain ⟨hbefore,hbetween,hafter⟩ := raw_layer_signature_bounds s k φ m L hm ell hrow t
  by_cases ha : t ≤ s.first (.inr k)
  · exact (hbefore ha).trans (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left (Nat.card (XP (X:=X) s k)) (Nat.mul_le_mul hy hp))
  · by_cases hb : t ≤ s.second (.inr k)
    · exact (hbetween (by omega) hb).trans (by simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_left (Nat.card (XP (X:=X) s k)*m^L) hy)
    · exact hafter (by omega)

end WeightedBooleanSharpness

section WeightedBooleanSharpness

variable {R S : Type} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
  {X Y Z : R → Type} [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)] [∀ i,Fintype (Z i)]
  [∀ i,Nonempty (X i)] [∀ i,Nonempty (Y i)]

/-- Full original-coordinate inputs; omitted designated coordinates and ignored
ordinary blocks are assigned fixed values. No coordinate is removed. -/
noncomputable def inputX (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (a : Table m ell) (x : XP (X:=X) s k) :
    ∀ i,FamilyX (X:=X) s k m ell i
  | .inl i => by
    classical
    exact if h:N s k i then x ⟨i,h⟩ else Classical.choice inferInstance
  | .inr j => by
    classical
    exact if h:j=k then (selectedX (X:=X) s k m ell j h).symm a
      else (otherX (X:=X) s k m ell j h).symm false

noncomputable def inputY (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (b : Table m ell) (y : YP (Y:=Y) s k) :
    ∀ i,FamilyY (Y:=Y) s k m ell i
  | .inl i => by
    classical
    exact if h:N s k i then y ⟨i,h⟩ else Classical.choice inferInstance
  | .inr j => by
    classical
    exact if h:j=k then (selectedY (Y:=Y) s k m ell j h).symm b
      else (otherY (Y:=Y) s k m ell j h).symm false

private theorem inputX_selected (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (a : Table m ell) (x : XP (X:=X) s k) :
    selectedX (X:=X) s k m ell k rfl (inputX s k m ell a x (.inr k))=a := by
  classical
  simp [inputX]

private theorem inputY_selected (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (b : Table m ell) (y : YP (Y:=Y) s k) :
    selectedY (Y:=Y) s k m ell k rfl (inputY s k m ell b y (.inr k))=b := by
  classical
  simp [inputY]

noncomputable def lowerPrefix (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (a : Table m ell) :
    Prefix (X:=X) (Y:=Y) s k m ell
      (firstRead s (.pair (.inr k) false)) (secondRead s (.pair (.inr k) false)) :=
  (fun i => inputX s k m ell a (Classical.choice inferInstance) i.val,
   fun i => inputY s k m ell 0 (Classical.choice inferInstance) i.val)

noncomputable def lowerSuffix (s : Skeleton (R ⊕ S)) (k : S) (m : ℕ)
    (ell : ZP (Z:=Z) s k → ℕ) (b : Table m ell)
    (x : XP (X:=X) s k) (y : YP (Y:=Y) s k) :
    Suffix (X:=X) (Y:=Y) s k m ell
      (firstRead s (.pair (.inr k) false)) (secondRead s (.pair (.inr k) false)) :=
  (fun i => inputX s k m ell 0 x i.val,fun i => inputY s k m ell b y i.val)

/-- All selector inputs remain in the one common suffix at this normalized cut. -/
private theorem lower_response (s : Skeleton (R ⊕ S)) (k : S)
    (φ : ∀ i,X i → Y i → Z i) (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ)
    (a b : Table m ell) (x : XP (X:=X) s k) (y : YP (Y:=Y) s k) :
    response (familyMap s k φ m ell) (familyOuter s k m ell)
      (firstRead s (.pair (.inr k) false)) (secondRead s (.pair (.inr k) false))
      (lowerPrefix (X:=X) (Y:=Y) s k m ell a) (lowerSuffix (X:=X) (Y:=Y) s k m ell b x y)=
      zeroTest (productMap s k φ) m ell a b x y := by
  classical
  let l := firstRead s (.pair (.inr k) false)
  let r := secondRead s (.pair (.inr k) false)
  have hk1 : l (.inr k) := le_rfl
  have hk2 : ¬r (.inr k) := by simp [r,secondRead]
  have hx : ∀ i : {i // N s k i},¬l (.inl i.val) := by
    intro i; exact not_le.mpr i.property.2.2
  have hy : ∀ i : {i // N s k i},¬r (.inl i.val) := by
    intro i
    have h:=i.property.2.2
    simpa [r,secondRead] using
      (not_lt.mpr h.le : ¬s.second (.inl i.val) < s.second (.inr k))
  have ex : joinX s k l
      (preX s k m ell l r (lowerPrefix (X:=X) (Y:=Y) s k m ell a))
      (sufX s k m ell l r (lowerSuffix (X:=X) (Y:=Y) s k m ell b x y))=x := by
    funext i
    simp [joinX,sufX,lowerSuffix,inputX,hx i,i.property]
  have ey : joinY s k r
      (preY s k m ell l r (lowerPrefix (X:=X) (Y:=Y) s k m ell a))
      (sufY s k m ell l r (lowerSuffix (X:=X) (Y:=Y) s k m ell b x y))=y := by
    funext i
    simp [joinY,sufY,lowerSuffix,inputY,hy i,i.property]
  rw [sharp_response_formula]
  change zeroTest _ _ _ _ _
    (joinX s k l _ _) (joinY s k r _ _)=_
  rw [ex,ey]
  simp [preA,sufA,preB,sufB,lowerPrefix,lowerSuffix,
    hk1,hk2,inputX_selected,inputY_selected,firstRead,secondRead]

/-- Actual distinct response functions, witnessed on the same labelled suffix:
select a differing table coordinate z and use the second table -a. -/
theorem normalized_table_injection (s : Skeleton (R ⊕ S)) (k : S)
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z)
    (m : ℕ) (ell : ZP (Z:=Z) s k → ℕ) :
    Function.Injective (fun a : Table m ell =>
      response (familyMap s k φ m ell) (familyOuter s k m ell)
        (firstRead s (.pair (.inr k) false)) (secondRead s (.pair (.inr k) false))
        (lowerPrefix (X:=X) (Y:=Y) s k m ell a)) := by
  classical
  intro a a' he
  funext z
  obtain ⟨x,y,hxy⟩ := productMap_onto s k φ hφ z
  subst z
  have h := congrFun he (lowerSuffix (X:=X) (Y:=Y) s k m ell (-a) x y)
  dsimp only at h
  rw [lower_response,lower_response] at h
  have hd : decide (a' (productMap s k φ x y)+-a (productMap s k φ x y)=0)=true := by
    simpa [zeroTest] using h.symm
  have hz : a' (productMap s k φ x y)+-a (productMap s k φ x y)=0 := of_decide_eq_true hd
  have heq : a' (productMap s k φ x y)=a (productMap s k φ x y) := eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hz)
  exact heq.symm

/-- Lower bound at the actual normalized layer immediately after k's first label. -/
theorem sharp_normalized_width_bound (s : Skeleton (R ⊕ S)) (k : S)
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z)
    (m : ℕ) [NeZero m] (ell : ZP (Z:=Z) s k → ℕ) :
    m^(∑ z,ell z) ≤ width (familyMap s k φ m ell) (familyOuter s k m ell) s.completion := by
  classical
  let c : Cut (R ⊕ S) := .pair (.inr k) false
  let f := response (familyMap s k φ m ell) (familyOuter s k m ell)
    (firstRead s c) (secondRead s c)
  let emb : Table m ell → Set.range f := fun a =>
    ⟨f (lowerPrefix (X:=X) (Y:=Y) s k m ell a),Set.mem_range_self _⟩
  have hi : Function.Injective emb := by
    intro a a' h
    exact normalized_table_injection s k φ hφ m ell (congrArg Subtype.val h)
  have hc : m^(∑ z,ell z) ≤ cutCard (familyMap s k φ m ell)
      (familyOuter s k m ell) (firstRead s c) (secondRead s c) := by
    have h := Nat.card_le_card_of_injective emb hi
    rw [table_card] at h
    exact h
  obtain ⟨ht,h1,h2⟩ := completion_prefix s c
  have he1 : (fun i => (s.completion (i,false)).val < cutSize s c)=firstRead s c := by
    funext i; exact propext (h1 i)
  have he2 : (fun i => (s.completion (i,true)).val < cutSize s c)=secondRead s c := by
    funext i; exact propext (h2 i)
  have hw := width_contains (familyMap s k φ m ell) (familyOuter s k m ell)
    s.completion (cutSize s c) ht
  rw [he1,he2] at hw
  exact hc.trans hw

end WeightedBooleanSharpness

section WeightedBooleanSharpness

variable {R S : Type} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
  [Nonempty S] {X Y Z : R → Type}
  [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)] [∀ i,Fintype (Z i)]
  [∀ i,Nonempty (X i)] [∀ i,Nonempty (Y i)]

noncomputable def localExponent (s : Skeleton (R ⊕ S))
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z) (k : S) : ℝ := by
  classical
  exact ∏ i : {i // N s k i},rowCoverNumber (φ i.val) (hφ i.val)

noncomputable def Theta (s : Skeleton (R ⊕ S))
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (localExponent s φ hφ)

private theorem localExponent_one_le (s : Skeleton (R ⊕ S))
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z) (k : S) :
    1 ≤ localExponent s φ hφ k := by
  classical
  apply Finset.one_le_prod
  intro i hi
  exact actualTau_one_le φ hφ i.val

set_option maxHeartbeats 1600000 in
/-- Finite maximization chooses k; no supplied maximum or sharpness hypothesis.
The returned integer certificate is the actual product-map dual certificate. -/
theorem attained_integer_certificate (s : Skeleton (R ⊕ S))
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z) :
    ∃ (k : S) (L : ℕ) (ell : ZP (Z:=Z) s k → ℕ),
      0 < L ∧ 1 ≤ Theta s φ hφ ∧ localExponent s φ hφ k=Theta s φ hφ ∧
      ((∑ z,ell z : ℕ):ℝ)=(L:ℝ)*Theta s φ hφ ∧
      (∀ x,(∑ z : Row (productMap s k φ) x,ell z.val) ≤ L) := by
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image Finset.univ
    (localExponent s φ hφ) Finset.univ_nonempty
  have he : localExponent s φ hφ k=Theta s φ hφ := by
    apply le_antisymm
    · exact Finset.le_sup' _ hk
    · exact Finset.sup'_le _ _ hmax
  have hT : 1 ≤ Theta s φ hφ := he ▸ localExponent_one_le s φ hφ k
  have hprod := productMap_onto s k φ hφ
  have hcover : rowCoverNumber (productMap s k φ) hprod=localExponent s φ hφ k := by
    exact product_cover_value (fun i : {i // N s k i} => φ i.val)
      (fun i => hφ i.val) hprod
  obtain ⟨L,ell,hL,htotal,hrow⟩ := integer_optimal_certificate (productMap s k φ) hprod
  rw [hcover,he] at htotal
  refine ⟨k,L,ell,hL,hT,he,htotal,?_⟩
  intro x
  apply le_trans ?_ (hrow x)
  apply le_of_eq
  apply Finset.sum_congr
  · ext z; simp
  · intro z hz; rfl

end WeightedBooleanSharpness

section WeightedBooleanSharpness

/-- A positive power eventually exceeds each fixed coefficient on integer moduli. -/
private theorem natural_rpow_unbounded (δ : ℝ) (hδ : 0 < δ) (K : ℝ) :
    ∃ m : ℕ,2 ≤ m ∧ K < (m:ℝ)^δ := by
  have hev : ∀ᶠ x : ℝ in Filter.atTop,K < x^δ :=
    (_root_.tendsto_rpow_atTop hδ).eventually (Filter.eventually_gt_atTop K)
  obtain ⟨b,hb⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨m,hm⟩ := exists_nat_gt (max b 2)
  have hmb : b ≤ (m:ℝ) := (le_max_left b 2).trans hm.le
  have hm2 : (2:ℝ) < m := (le_max_right b 2).trans_lt hm
  exact ⟨m,by exact_mod_cast hm2.le,hb m hmb⟩

/-- Both signs of alpha are covered. For alpha < 0, only Wpi≥1 is needed. -/
private theorem separating_modulus (L M : ℕ) (Θ α C c : ℝ)
    (hL : 0 < L) (hΘ : 1 ≤ Θ) (hM : (M:ℝ)=(L:ℝ)*Θ)
    (hα : α < Θ) (hC : 0 < C) (hc : 0 < c) :
    ∃ m : ℕ,2 ≤ m ∧ ∀ w : ℝ,1 ≤ w → w ≤ c*(m:ℝ)^L → C*w^α < (m:ℝ)^M := by
  have hLr : (0:ℝ) < L := by exact_mod_cast hL
  have hΘ0 : 0 < Θ := lt_of_lt_of_le zero_lt_one hΘ
  have hMr : (0:ℝ) < M := by rw [hM]; positivity
  by_cases hneg : α < 0
  · obtain ⟨m,hm,hgrow⟩ := natural_rpow_unbounded M hMr C
    refine ⟨m,hm,?_⟩
    intro w hw hwu
    have hpow : w^α ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1) hw hneg.le
    have hh := mul_le_mul_of_nonneg_left hpow hC.le
    have hsmall : C*w^α ≤ C := by simpa using hh
    exact hsmall.trans_lt (by simpa only [Real.rpow_natCast] using hgrow)
  · have hα0 : 0 ≤ α := le_of_not_gt hneg
    let δ := (M:ℝ)-(L:ℝ)*α
    have hδ : 0 < δ := by dsimp [δ]; rw [hM]; nlinarith
    obtain ⟨m,hm,hgrow⟩ := natural_rpow_unbounded δ hδ (C*c^α)
    have hmr : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hpowpos : 0 < (m:ℝ)^((L:ℝ)*α) := Real.rpow_pos_of_pos hmr _
    have hcalc : C*(c*(m:ℝ)^L)^α < (m:ℝ)^M := by
      calc
        C*(c*(m:ℝ)^L)^α = (C*c^α)*(m:ℝ)^((L:ℝ)*α) := by
          rw [Real.mul_rpow hc.le (by positivity),Real.rpow_mul hmr.le,Real.rpow_natCast]
          ring
        _ < (m:ℝ)^δ*(m:ℝ)^((L:ℝ)*α) := mul_lt_mul_of_pos_right hgrow hpowpos
        _ = (m:ℝ)^M := by
          rw [←Real.rpow_add hmr]
          have he : δ+(L:ℝ)*α=(M:ℝ) := by dsimp [δ]; ring
          rw [he,Real.rpow_natCast]
    refine ⟨m,hm,?_⟩
    intro w hw hwu
    have hmono := Real.rpow_le_rpow (by linarith : 0 ≤ w) hwu hα0
    exact (mul_le_mul_of_nonneg_left hmono hC.le).trans_lt hcalc

variable {R S : Type} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
  [Nonempty S] {X Y Z : R → Type}
  [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)] [∀ i,Fintype (Z i)]
  [∀ i,Nonempty (X i)] [∀ i,Nonempty (Y i)]

/-- One actual maximizing ordinary block defeats every smaller real exponent.
The fixed k, L and ell are chosen before alpha and C; only m and G then vary. -/
theorem scalar_boolean_subcritical_failure (s : Skeleton (R ⊕ S))
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z) :
    ∃ (k : S) (L : ℕ) (ell : ZP (Z:=Z) s k → ℕ),
      0 < L ∧ localExponent s φ hφ k=Theta s φ hφ ∧
      (∀ m : ℕ,FamilyAllowed s k φ m ell) ∧
      ∀ (α C : ℝ),α < Theta s φ hφ → 0 < C → ∃ (m : ℕ) (hm : 2 ≤ m),
          letI : NeZero m := ⟨by omega⟩
          C*(width (familyMap s k φ m ell) (familyOuter s k m ell) s.position : ℝ)^α < (width (familyMap s k φ m ell) (familyOuter s k m ell) s.completion : ℝ) := by
  obtain ⟨k,L,ell,hL,hΘ,he,htotal,hrow⟩ := attained_integer_certificate s φ hφ
  refine ⟨k,L,ell,hL,he,(fun m => family_allowed s k φ hφ m ell),?_⟩
  intro α C hα hC
  let c : ℝ := Nat.card (XP (X:=X) s k)*Nat.card (YP (Y:=Y) s k)
  have hx : 0 < Nat.card (XP (X:=X) s k) := Nat.card_pos
  have hy : 0 < Nat.card (YP (Y:=Y) s k) := Nat.card_pos
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨m,hm,hsep⟩ := separating_modulus L (∑ z,ell z)
    (Theta s φ hφ) α C c hL hΘ htotal hα hC hc
  refine ⟨m,hm,?_⟩
  letI : NeZero m := ⟨by omega⟩
  obtain ⟨hpos,hub⟩ := sharp_original_width_bound s k φ m L hm ell hrow
  have hlow := sharp_normalized_width_bound s k φ hφ m ell
  have hp : (1:ℝ) ≤ width (familyMap s k φ m ell) (familyOuter s k m ell) s.position := by
    exact_mod_cast hpos
  have hu : (width (familyMap s k φ m ell) (familyOuter s k m ell) s.position : ℝ) ≤ c*(m:ℝ)^L := by
    dsimp [c]; exact_mod_cast hub
  have hl : (m:ℝ)^(∑ z,ell z) ≤ (width (familyMap s k φ m ell) (familyOuter s k m ell) s.completion : ℝ) := by
    exact_mod_cast hlow
  exact (hsep _ hp hu).trans_le hl

end WeightedBooleanSharpness

section WeightedBooleanSharpness

variable {R S : Type} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
  [Nonempty S]

def IsDesignated : R ⊕ S → Prop
  | .inl _ => True
  | .inr _ => False

section ThetaIdentity
variable {X Y Z : R → Type}
  [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)] [∀ i,Fintype (Z i)]
  [∀ i,Nonempty (X i)] [∀ i,Nonempty (Y i)]

/-- Only designated weights enter each strict containment neighborhood. -/
private theorem neighborhood_restriction (s : Skeleton (R ⊕ S))
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z)
    (τ : R ⊕ S → ℝ) (hτ : ∀ i,τ (.inl i)=rowCoverNumber (φ i) (hφ i)) (k : S) :
    productOn (neighborhood s IsDesignated (.inr k)) τ=localExponent s φ hφ k := by
  classical
  calc
    productOn (neighborhood s IsDesignated (.inr k)) τ =
        ∏ i : R,if N s k i then τ (.inl i) else 1 := by
      simp [productOn,Fintype.prod_sum_type,neighborhood,IsDesignated,N]
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : N s k i <;> simp only [N] at h ⊢ <;> simp [h]
    _ = ∏ i : R,if N s k i then rowCoverNumber (φ i) (hφ i) else 1 := by
      simp only [hτ]
    _ = localExponent s φ hφ k := by
      exact (productOn_subtype (N s k) (fun i => rowCoverNumber (φ i) (hφ i))).symm

/-- The upper bridge's maximum equals the fixed designated-family maximum. -/
private theorem theta_restriction (s : Skeleton (R ⊕ S))
    (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z)
    (τ : R ⊕ S → ℝ) (hτ : ∀ i,τ (.inl i)=rowCoverNumber (φ i) (hφ i))
    (ho : ∃ i : R ⊕ S,¬IsDesignated i) :
    theta s IsDesignated τ ho=Theta s φ hφ := by
  classical
  dsimp [theta,Theta]
  apply le_antisymm
  · refine Finset.sup'_le _ _ ?_
    intro j hj
    cases j with
    | inl i =>
      have hn := (Finset.mem_filter.mp hj).2
      exact (hn trivial).elim
    | inr k =>
      rw [neighborhood_restriction s φ hφ τ hτ]
      exact Finset.le_sup' _ (Finset.mem_univ k)
  · refine Finset.sup'_le _ _ ?_
    intro k hk
    rw [←neighborhood_restriction s φ hφ τ hτ k]
    exact neighborhood_le_theta s IsDesignated τ ho (.inr k) (by simp [IsDesignated])

end ThetaIdentity

section OriginalContract
variable [Nonempty R] {O : Type} [Fintype O] [Nonempty O]
  {U V W : R ⊕ S → Type}
  [∀ i,Fintype (U i)] [∀ i,Fintype (V i)] [∀ i,Fintype (W i)]
  [∀ i,Nonempty (U i)] [∀ i,Nonempty (V i)]

/-- Uniform upper bound for every allowed actual ordinary family, together with
one designated-family construction refuting every smaller exponent using Bool.
Constants in the upper bound involve only the fixed designated restriction.
-/
theorem original33_bound_and_boolean_obstruction
    (s : Skeleton (R ⊕ S)) (ψ : ∀ i,U i → V i → W i) (G : (∀ i,W i) → O)
    (hd : ∀ i : R,∀ z,∃ x y,ψ (.inl i) x y=z)
    (ho : ∀ j : S,
      (∃ a,Function.Surjective (ψ (.inr j) a)) ∧
      (∃ b,Function.Surjective (fun a => ψ (.inr j) a b))) :
    let φ := fun i : R => ψ (.inl i)
    let D : ℕ := ∏ i : R,Fintype.card (U (.inl i))*Fintype.card (V (.inl i))
    let T : ℝ := ∏ i : R,rowCoverNumber (φ i) (hd i)
    let old : ℝ := labelledWidth ψ G s.position
    (labelledWidth ψ G s.completion : ℝ) ≤ min (old^T) ((D:ℝ)*old^(Theta s φ hd)) ∧
    ∃ (k : S) (L : ℕ) (ell : ZP (Z:=fun i : R => W (.inl i)) s k → ℕ),
      0 < L ∧ localExponent s φ hd k=Theta s φ hd ∧
      (∀ m : ℕ,FamilyAllowed s k φ m ell) ∧
      ∀ (α C : ℝ),α < Theta s φ hd → 0 < C → ∃ (m : ℕ) (hm : 2 ≤ m),
          letI : NeZero m := ⟨by omega⟩
          C*(labelledWidth (familyMap s k φ m ell) (familyOuter s k m ell) s.position : ℝ)^α < (labelledWidth (familyMap s k φ m ell) (familyOuter s k m ell) s.completion : ℝ) := by
  let φ := fun i : R => ψ (.inl i)
  have hψ : ∀ i z,∃ x y,ψ i x y=z := by
    intro i z
    cases i with
    | inl i => exact hd i z
    | inr j =>
      obtain ⟨a,ha⟩ := (ho j).1
      obtain ⟨b,hb⟩ := ha z
      exact ⟨a,b,hb⟩
  have hord : ∀ i : R ⊕ S,¬IsDesignated i → (∃ a,Function.Surjective (ψ i a)) ∧
      (∃ b,Function.Surjective (fun a => ψ i a b)) := by
    intro i hi
    cases i with
    | inl i => exact (hi trivial).elim
    | inr j => exact ho j
  have hindex : ∃ i : R ⊕ S,¬IsDesignated i :=
    ⟨.inr (Classical.choice inferInstance),by simp [IsDesignated]⟩
  have hτ : ∀ i : R,actualTau ψ hψ (.inl i)=rowCoverNumber (φ i) (hd i) := by
    intro i; rfl
  have hΘ := theta_restriction s φ hd (actualTau ψ hψ) hτ hindex
  have hT : productOn IsDesignated (actualTau ψ hψ)=
      ∏ i : R,rowCoverNumber (φ i) (hd i) := by
    simp [productOn,Fintype.prod_sum_type,IsDesignated,hτ]
  have hD : (∏ i : {i : R ⊕ S // IsDesignated i},
      Fintype.card (U i.val)*Fintype.card (V i.val) : ℕ)=
      ∏ i : R,Fintype.card (U (.inl i))*Fintype.card (V (.inl i)) := by
    let e : {i : R ⊕ S // IsDesignated i} ≃ R :=
      { toFun := fun i => match i with
          | ⟨.inl j,_⟩ => j
          | ⟨.inr j,h⟩ => False.elim h
        invFun := fun j => ⟨.inl j,trivial⟩
        left_inv := by intro i; rcases i with ⟨i,h⟩; cases i with
          | inl j => rfl
          | inr j => exact False.elim h
        right_inv := by intro j; rfl }
    apply Fintype.prod_equiv e
    intro i
    rcases i with ⟨i,h⟩
    cases i with
    | inl j => rfl
    | inr j => exact False.elim h
  constructor
  · have hh := (original_labelled_upper_contract ψ G hψ s IsDesignated hindex hord).1
    rw [hT,hD,hΘ] at hh
    exact hh
  · obtain ⟨k,L,ell,hL,he,hfam,hfail⟩ := scalar_boolean_subcritical_failure s φ hd
    refine ⟨k,L,ell,hL,he,hfam,?_⟩
    intro α C hα hC
    obtain ⟨m,hm,h⟩ := hfail α C hα hC
    refine ⟨m,hm,?_⟩
    letI : NeZero m := ⟨by omega⟩
    simpa only [labelled_width_eq] using h

end OriginalContract
end WeightedBooleanSharpness

end D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion
