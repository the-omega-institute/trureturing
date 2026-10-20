/- GID: D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/CutBounds
   generality: I
   mirror-B: D5/B/S3/Observer/Separation/FixedSkeletonWeightedInclusion/CutBounds
   mirror-E: none(waiver:symbolic-existence-and-bounds)
   anchors: []
   utility: none
   digest: Actual relation supports and grouped responses bound every original labelled layer. -/

import D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.RowCertificates
import D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.LabelledResponses

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.CutBounds

open D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.RowCertificates
open D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.LabelledResponses
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.Forgetting.PushforwardComposition
open D5.S3.Entropy.Forgetting.CompletionEntropyMinimality
open D5.S3.Entropy.Forgetting.DeterministicEntropyEquality
open scoped Classical

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

theorem width_contains (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O)
    (p : Endpoint I ≃ Fin (2*Fintype.card I)) (t : ℕ) (ht : t ≤ 2*Fintype.card I) :
    cutCard φ G (fun i => (p (i,false)).val < t) (fun i => (p (i,true)).val < t) ≤ width φ G p := by
  classical
  exact Finset.le_sup (f := fun t => cutCard φ G (fun i => (p (i,false)).val < t) (fun i => (p (i,true)).val < t)) (Finset.mem_range.mpr (by omega))

theorem width_pos (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O)
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

theorem productOn_subtype (P : I → Prop) (τ : I → ℝ) :
    (∏ i : {i // P i}, τ i.val)=productOn P τ := by
  classical
  have h := Finset.prod_subtype (p := P) (F := inferInstance) (Finset.univ.filter P)
    (by intro i; simp) τ
  rw [Finset.prod_filter] at h
  exact h.symm

private theorem productOn_mono (A B : I → Prop) (τ : I → ℝ)
    (hτ : ∀ i, 1 ≤ τ i) (h : ∀ i, A i → B i) : productOn A τ ≤ productOn B τ := by
  classical
  apply Finset.prod_le_prod₀
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

theorem actualTau_one_le (φ : ∀ i,X i → Y i → Z i) (hφ : ∀ i z,∃ x y,φ i x y=z) :
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

theorem neighborhood_le_theta (s : Skeleton I) (designated : I → Prop) (τ : I → ℝ)
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

theorem labelled_width_eq (φ : ∀ i,X i → Y i → Z i) (G : (∀ i,Z i) → O)
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

end D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.CutBounds
