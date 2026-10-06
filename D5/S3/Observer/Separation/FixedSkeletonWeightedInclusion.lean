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

end D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion
