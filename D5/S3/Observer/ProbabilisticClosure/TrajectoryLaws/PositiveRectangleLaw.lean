/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Supported rectangular words are excluded on the actual full-erasure output law. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleMessages
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ErasedExteriorFiltration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateFullErasure
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateGhost

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Function Set Filter
open scoped BigOperators Matrix Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open MarkedPredictiveQuotient OriginalLawTrimming OriginalMarkedLaw
open OriginalErasureComparison ErasedExteriorFiltration PositiveRectangleMessages

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleLaw
variable {H : Type*} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]

def product (θ : Presentation H) (w : List Bool) : Matrix H H ℝ :=
  (w.map θ.matrix).prod

def block (t : ℤ) (w : List Bool) : Set (ℤ → Bool) :=
  {z | ∀ k : Fin w.length, z (t+k.val) = w.get k}

theorem product_word (θ : Presentation H) (w : List Bool) :
    product θ w = wordMatrix θ.matrix w.length w.get := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    change θ.matrix x * product θ w = θ.matrix x * wordMatrix θ.matrix w.length (Fin.tail (x::w).get)
    rw [ih]
    congr 2

private theorem block_mass (θ : Presentation H) (t : ℤ) (w : List Bool) :
    (visibleLaw θ : Measure _).real (block t w) =
      ∑ i, ∑ j, θ.initial i * product θ w i j := by
  have h := (same_law_trimming θ).2.2.2.2.2.2.2.1 t w.length w.get
  change (visibleLaw θ : Measure _).real (block t w) = _ at h
  rw [h]
  simp only [futureMass,← product_word,Finset.mul_sum]

theorem block_append (t : ℤ) (u v : List Bool) :
    block t (u++v) = block t u ∩ block (t+u.length) v := by
  ext z
  simp only [block,Set.mem_setOf_eq,Set.mem_inter_iff]
  constructor
  · intro h
    constructor
    · intro k
      have hh := h (⟨k.val,by simp only [List.length_append]; omega⟩ : Fin (u++v).length)
      simpa only [List.get_eq_getElem,List.getElem_append_left k.isLt] using hh
    · intro k
      have hh := h (⟨u.length+k.val,by simp only [List.length_append]; omega⟩ : Fin (u++v).length)
      simp only [List.get_eq_getElem,List.getElem_append_right (by omega : u.length ≤ u.length+k.val),
        Nat.add_sub_cancel_left,Nat.cast_add,add_assoc] at hh
      simpa only [List.get_eq_getElem,add_assoc] using hh
  · rintro ⟨hu,hv⟩ k
    simp only [List.get_eq_getElem]
    by_cases hk : k.val < u.length
    · rw [List.getElem_append_left hk]
      exact hu ⟨k.val,hk⟩
    · rw [List.getElem_append_right (by omega : u.length ≤ k.val)]
      have hh := hv (⟨k.val-u.length,by have := k.isLt; simp only [List.length_append] at this; omega⟩ : Fin v.length)
      simp only [List.get_eq_getElem] at hh
      rw [← hh]
      congr 1
      rw [Int.natCast_sub (by omega)]
      ring

theorem product_nonneg (θ : Presentation H) (w : List Bool) (i j : H) :
    0 ≤ product θ w i j := by
  induction w generalizing i with
  | nil => simp [product,Matrix.one_apply]; split_ifs <;> norm_num
  | cons x w ih =>
    simp only [product,List.map_cons,List.prod_cons,Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (θ.matrix_nonneg x i k) (ih k)

private theorem centered_mass (θ : Presentation H) (r : ℕ) (u v : Fin r → Bool) (x : Bool) :
    (visibleLaw θ : Measure _).real {z | window r z = (u,v) ∧ z 0 = x} =
      ∑ i, ∑ j, θ.initial i *
        (product θ (List.ofFn u) * θ.matrix x * product θ (List.ofFn v)) i j := by
  have he : {z | window r z = (u,v) ∧ z 0 = x} =
      block (-(r:ℤ)) (List.ofFn u ++ [x] ++ List.ofFn v) := by
    rw [block_append,block_append]
    ext z
    simp only [List.length_ofFn,List.length_append,List.length_singleton,block,
      Set.mem_setOf_eq,Set.mem_inter_iff,window,Prod.mk.injEq,funext_iff]
    constructor
    · rintro ⟨⟨hu,hv⟩,hx⟩
      refine ⟨⟨?_,?_⟩,?_⟩
      · intro k; simpa [leftWord] using hu ⟨k.val,by simpa using k.isLt⟩
      · intro k; fin_cases k; simpa using hx
      · intro k; simpa [rightWord,add_comm] using hv ⟨k.val,by simpa using k.isLt⟩
    · rintro ⟨⟨hu,hx⟩,hv⟩
      refine ⟨⟨?_,?_⟩,?_⟩
      · intro k; simpa [leftWord] using hu ⟨k.val,by simpa using k.isLt⟩
      · intro k; simpa [rightWord,add_comm] using hv ⟨k.val,by simpa using k.isLt⟩
      · simpa using hx 0
  rw [he,block_mass]
  simp only [product,List.map_append,List.prod_append,List.map_singleton,List.prod_singleton]

private theorem window_mass (θ : Presentation H) (r : ℕ) (u v : Fin r → Bool) :
    (visibleLaw θ : Measure _).real {z | window r z = (u,v)} =
      (∑ i, ∑ j, θ.initial i *
        (product θ (List.ofFn u) * θ.matrix false * product θ (List.ofFn v)) i j) +
      (∑ i, ∑ j, θ.initial i *
        (product θ (List.ofFn u) * θ.matrix true * product θ (List.ofFn v)) i j) := by
  let μ := (visibleLaw θ : Measure (ℤ → Bool))
  letI : IsProbabilityMeasure μ := by change IsProbabilityMeasure (visibleLaw θ : Measure (ℤ → Bool)); infer_instance
  have hm : Measurable (window r) := by unfold window leftWord rightWord; fun_prop
  have he : {z | window r z = (u,v)} =
      {z | window r z = (u,v) ∧ z 0 = false} ∪ {z | window r z = (u,v) ∧ z 0 = true} := by
    ext z; cases hx : z 0 <;> simp [hx]
  have hden : μ.real {z | window r z = (u,v)} =
      μ.real {z | window r z = (u,v) ∧ z 0 = false} +
      μ.real {z | window r z = (u,v) ∧ z 0 = true} := by
    conv_lhs => rw [he]
    refine measureReal_union ?_ ?_
    · exact Set.disjoint_left.mpr fun z hz₀ hz₁ => Bool.false_ne_true (hz₀.2.symm.trans hz₁.2)
    · exact (hm (measurableSet_singleton _)).inter
        ((measurableSet_singleton true).preimage (measurable_pi_apply (0:ℤ)))
  exact hden.trans (congrArg₂ (·+·) (centered_mass θ r u v false) (centered_mass θ r u v true))

private theorem centered_ratio (θ : Presentation H) (r : ℕ) (u v : Fin r → Bool)
    (hpos : 0 < (visibleLaw θ : Measure _).real {z | window r z = (u,v)}) :
    bitPredictor (visibleLaw θ : Measure _) (fun z => z 0) (window r) (u,v) =
      (∑ i, ∑ j, θ.initial i *
        (product θ (List.ofFn u) * θ.matrix true * product θ (List.ofFn v)) i j) /
      ((∑ i, ∑ j, θ.initial i *
        (product θ (List.ofFn u) * θ.matrix false * product θ (List.ofFn v)) i j) +
       (∑ i, ∑ j, θ.initial i *
        (product θ (List.ofFn u) * θ.matrix true * product θ (List.ofFn v)) i j)) := by
  let μ := (visibleLaw θ : Measure (ℤ → Bool))
  letI : IsProbabilityMeasure μ := by change IsProbabilityMeasure (visibleLaw θ : Measure (ℤ → Bool)); infer_instance
  have hm : Measurable (window r) := by unfold window leftWord rightWord; fun_prop
  have he : {z | window r z = (u,v)} =
      {z | window r z = (u,v) ∧ z 0 = false} ∪ {z | window r z = (u,v) ∧ z 0 = true} := by
    ext z; cases hx : z 0 <;> simp [hx]
  have hden : μ.real {z | window r z = (u,v)} =
      μ.real {z | window r z = (u,v) ∧ z 0 = false} +
      μ.real {z | window r z = (u,v) ∧ z 0 = true} := by
    conv_lhs => rw [he]
    refine measureReal_union ?_ ?_
    · exact Set.disjoint_left.mpr fun z hz₀ hz₁ => Bool.false_ne_true (hz₀.2.symm.trans hz₁.2)
    · exact (hm (measurableSet_singleton _)).inter
        ((measurableSet_singleton true).preimage (measurable_pi_apply (0:ℤ)))
  have hn : μ.map (window r) {(u,v)} ≠ 0 := by
    rw [Measure.map_apply hm (measurableSet_singleton _)]
    change μ {z | window r z = (u,v)} ≠ 0
    exact fun h => hpos.ne' (by change (μ _).toReal = 0; rw [h]; rfl)
  change ((ProbabilityTheory.condDistrib (fun z : ℤ → Bool => z 0) (window r) μ (u,v)) {true}).toReal = _
  rw [ProbabilityTheory.condDistrib_apply_of_ne_zero hm (measurable_pi_apply 0) (u,v) hn,
    ENNReal.toReal_mul, ENNReal.toReal_inv,
    Measure.map_apply hm (measurableSet_singleton _),
    Measure.map_apply (hm.prodMk (measurable_pi_apply 0))
      ((measurableSet_singleton _).prod (measurableSet_singleton _))]
  change (μ.real {z | window r z = (u,v)})⁻¹ * μ.real {z | window r z = (u,v) ∧ z 0 = true} = _
  rw [hden,centered_mass,centered_mass]
  ring

private theorem read_block (z : ℤ → Bool) (t : ℤ) (n : ℕ) :
    z ∈ block t (List.ofFn fun k : Fin n => z (t+k.val)) := by
  intro k
  simp

private theorem block_unique (t : ℤ) (u v : List Bool) (hlen : u.length = v.length)
    (z : ℤ → Bool) (hu : z ∈ block t u) (hv : z ∈ block t v) : u = v := by
  apply List.ext_get hlen
  intro i hi hv'
  exact (hu ⟨i,hi⟩).symm.trans (hv ⟨i,hv'⟩)

/-- The protected exterior fixes w0 before the missing center and 0w after it. -/
def guard (w : List Bool) : Set (ℤ → Bool) :=
  block (-((w.length+1:ℕ):ℤ)) (w++[false]) ∩ block 1 (false::w)

private theorem farther_words (w : List Bool) (r : ℕ) (hr : w.length+1 ≤ r)
    (z : ℤ → Bool) (hz : z ∈ guard w) :
    ∃ a b : List Bool,
      List.ofFn (leftWord r z) = a++w++[false] ∧
      List.ofFn (rightWord r z) = (false::w)++b := by
  let m := r-(w.length+1)
  let a := List.ofFn fun k : Fin m => z (-(r:ℤ)+k.val)
  let b := List.ofFn fun k : Fin m => z ((w.length:ℤ)+2+k.val)
  have ha : z ∈ block (-(r:ℤ)) a := read_block z _ m
  have hb : z ∈ block ((w.length:ℤ)+2) b := read_block z _ m
  have hleft : z ∈ block (-(r:ℤ)) (a++(w++[false])) := by
    rw [block_append]
    refine ⟨ha,?_⟩
    have he : -(r:ℤ)+(a.length:ℤ) = -((w.length+1:ℕ):ℤ) := by
      dsimp [a,m]; simp only [List.length_ofFn]; omega
    rw [he]
    exact hz.1
  have hright : z ∈ block 1 ((false::w)++b) := by
    rw [block_append]
    refine ⟨hz.2,?_⟩
    convert hb using 2 <;> simp <;> ring
  refine ⟨a,b,?_,?_⟩
  · apply block_unique (-(r:ℤ)) _ _ (by simp [a,m]; omega) z
    · exact read_block z _ r
    · simpa only [List.append_assoc] using hleft
  · apply block_unique 1 _ _ (by simp [b,m]; omega) z
    · change z ∈ block 1 (List.ofFn fun k : Fin r => z (k.val+1))
      simpa only [add_comm] using read_block z 1 r
    · exact hright

private theorem sandwich_factor (θ : Presentation H) (T B A C : Matrix H H ℝ) :
    (∑ i, ∑ j, θ.initial i * (A*T*B*T*C) i j) =
      sandwich T B (fun k => ∑ i, θ.initial i*A i k) (fun l => ∑ j, C l j) := by
  have hs (α β : H → ℝ) : sandwich T B α β =
      (α ᵥ* T) ⬝ᵥ (B *ᵥ (T *ᵥ β)) := by
    rw [Matrix.dot_mulVec_eq_sum_sum,Finset.sum_comm]
    rfl
  rw [hs]
  have he : (fun k => ∑ i, θ.initial i*A i k) = θ.initial ᵥ* A := rfl
  rw [he]
  have he' : (fun l => ∑ j, C l j) = C *ᵥ (fun _ => (1:ℝ)) := by
    funext l
    simp [Matrix.mulVec,dotProduct]
  rw [he',Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec]
  simp only [Matrix.vecMul_vecMul,← Matrix.mul_assoc]
  simp only [Matrix.vecMul,dotProduct,mul_one,Finset.sum_mul]
  exact Finset.sum_comm

private theorem window_positive (θ : Presentation H) (r : ℕ) :
    ∀ᵐ z ∂(visibleLaw θ : Measure (ℤ → Bool)),
      0 < (visibleLaw θ : Measure _).real {y | window r y = window r z} := by
  let μ := (visibleLaw θ : Measure (ℤ → Bool))
  have hm : Measurable (window r) := by unfold window leftWord rightWord; fun_prop
  have h (w : (Fin r → Bool) × (Fin r → Bool)) : ∀ᵐ z ∂μ,
      window r z = w → 0 < μ.real {y | window r y = w} := by
    by_cases hp : 0 < μ.real {y | window r y = w}
    · exact Eventually.of_forall fun _ _ => hp
    · have hz : μ {y | window r y = w} = 0 :=
        (measureReal_eq_zero_iff (μ := μ)).mp (le_antisymm (le_of_not_gt hp) measureReal_nonneg)
      have hae : ∀ᵐ z ∂μ, window r z ≠ w := by simpa only [ae_iff,not_not] using hz
      exact hae.mono fun z hz he => (hz he).elim
  have hh := ae_all_iff.mpr h
  exact hh.mono fun z hz => hz (window r z) rfl

private theorem protected_mass (θ : Presentation H) (w : List Bool) (x : Bool) :
    (visibleLaw θ : Measure _).real (block (-((w.length+1:ℕ):ℤ))
      (w++[false,x,false]++w)) =
    sandwich (product θ w) (θ.matrix false*θ.matrix x*θ.matrix false) θ.initial (fun _ => 1) := by
  rw [block_mass]
  have hh := sandwich_factor θ (product θ w) (θ.matrix false*θ.matrix x*θ.matrix false) 1 1
  simpa only [product,List.map_append,List.prod_append,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,Matrix.mul_one,Matrix.one_mul,Matrix.mul_assoc,Matrix.one_apply,
    mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hh

private theorem actual_finite_guard (θ : Presentation H) (w : List Bool)
    (R : Rectangle (product θ w))
    (hp : ∀ x, 0 < (visibleLaw θ : Measure _).real
      (block (-((w.length+1:ℕ):ℤ)) (w++[false,x,false]++w))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r, w.length+1 ≤ r →
      ∀ᵐ z ∂(visibleLaw θ : Measure (ℤ → Bool)), z ∈ guard w →
        ε ≤ finiteMean θ r z ∧ finiteMean θ r z ≤ 1-ε := by
  let B (x : Bool) := θ.matrix false*θ.matrix x*θ.matrix false
  have hB (x : Bool) (i j : H) : 0 ≤ B x i j := by
    simpa only [product,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      Matrix.mul_one,Matrix.mul_assoc,B] using product_nonneg θ [false,x,false] i j
  obtain ⟨ε,hε,_,he⟩ := supported_message_guard (product θ w) (B false) (B true) R
    (hB false) (hB true) θ.initial θ.initial_nonneg
    (by rw [← protected_mass]; exact hp false) (by rw [← protected_mass]; exact hp true)
  refine ⟨ε,hε,?_⟩
  intro r hr
  filter_upwards [window_positive θ r] with z hz hG
  obtain ⟨a,b,ha,hb⟩ := farther_words w r hr z hG
  let α : H → ℝ := fun k => ∑ i, θ.initial i*product θ a i k
  let β : H → ℝ := fun l => ∑ j, product θ b l j
  have hα (i : H) : 0 ≤ α i := Finset.sum_nonneg fun j _ =>
    mul_nonneg (θ.initial_nonneg j) (product_nonneg θ a j i)
  have hβ (i : H) : 0 ≤ β i := Finset.sum_nonneg fun j _ => product_nonneg θ b i j
  have hc (x : Bool) : (∑ i, ∑ j, θ.initial i *
      (product θ (List.ofFn (leftWord r z)) * θ.matrix x *
        product θ (List.ofFn (rightWord r z))) i j) = sandwich (product θ w) (B x) α β := by
    rw [ha,hb]
    have hh := sandwich_factor θ (product θ w) (B x) (product θ a) (product θ b)
    simpa only [product,List.map_append,List.prod_append,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,Matrix.mul_one,Matrix.mul_assoc,B,α,β] using hh
  have htotal : 0 < sandwich (product θ w) (B false) α β +
      sandwich (product θ w) (B true) α β := by
    rw [← hc false,← hc true,← window_mass]
    exact hz
  have hg := he α β hα hβ htotal
  change ε ≤ bitPredictor (visibleLaw θ : Measure _) (fun z => z 0) (window r)
      (leftWord r z,rightWord r z) ∧
    bitPredictor (visibleLaw θ : Measure _) (fun z => z 0) (window r)
      (leftWord r z,rightWord r z) ≤ 1-ε
  rw [centered_ratio θ r _ _ hz,hc false,hc true]
  exact hg

private def allowed : Bool → List Bool → Prop
  | _, [] => True
  | b, x::w => ¬(b = true ∧ x = true) ∧ allowed x w

private theorem allowed_native (b : Bool) (w : List Bool) :
    allowed b w ↔ TwelveStatePresentation.Allowed b w.length w.get := by
  induction w generalizing b with
  | nil => rfl
  | cons x w ih =>
    change (¬(b = true ∧ x = true) ∧ allowed x w) ↔
      (¬(b = true ∧ x = true) ∧ TwelveStatePresentation.Allowed x w.length (Fin.tail (x::w).get))
    exact and_congr_right fun _ => ih x

private theorem allowed_zero_append (b : Bool) (u v : List Bool)
    (hu : allowed b u) (hv : allowed false v) : allowed b (u++false::v) := by
  induction u generalizing b with
  | nil => simpa [allowed] using hv
  | cons x u ih => exact ⟨hu.1,ih x hu.2⟩

private theorem exclusion (θ : Presentation H)
    (hfull : fullMean θ =ᵐ[(visibleLaw θ : Measure (ℤ → Bool))] erasedBit)
    (hsupport : ∀ t n w, 0 < (visibleLaw θ : Measure _).real (visibleCylinder t n w) ↔
      TwelveStatePresentation.Legal n w)
    (w : List Bool) (hw : 0 < (visibleLaw θ : Measure _).real (block 0 w)) :
    ¬ Nonempty (Rectangle (product θ w)) := by
  rintro ⟨R⟩
  have hlegal : allowed false w := (allowed_native false w).mpr ((hsupport 0 w.length w.get).mp hw)
  have hp (x : Bool) : 0 < (visibleLaw θ : Measure _).real
      (block (-((w.length+1:ℕ):ℤ)) (w++[false,x,false]++w)) := by
    apply (hsupport _ _ _).mpr
    apply (allowed_native false _).mp
    have hh : allowed false (x::false::w) := by cases x <;> simpa [allowed] using hlegal
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using
      allowed_zero_append false w (x::false::w) hlegal hh
  have hG : 0 < (visibleLaw θ : Measure (ℤ → Bool)) (guard w) := by
    have hsub : block (-((w.length+1:ℕ):ℤ)) (w++[false,false,false]++w) ⊆ guard w := by
      have he : block (-((w.length+1:ℕ):ℤ)) (w++[false,false,false]++w) =
          block (-((w.length+1:ℕ):ℤ)) (w++[false]) ∩ block 0 (false::false::w) := by
        convert block_append (-((w.length+1:ℕ):ℤ)) (w++[false]) (false::false::w) using 2 <;> simp
      intro z hz
      rw [he] at hz
      have hh : z ∈ block 0 ([false]++(false::w)) := hz.2
      rw [block_append] at hh
      exact ⟨hz.1,by simpa using hh.2⟩
    exact (ENNReal.toReal_pos_iff.mp (hp false)).1.trans_le (measure_mono hsub)
  obtain ⟨ε,hε,hguard⟩ := actual_finite_guard θ w R hp
  exact no_uniform_exterior_guard θ hfull (guard w) hG ε hε (w.length+1) hguard

theorem product_ofFn (θ : Presentation H) (n : ℕ) (w : Fin n → Bool) :
    product θ (List.ofFn w) = wordMatrix θ.matrix n w := by
  induction n with
  | zero => simp [product,wordMatrix]
  | succ n ih =>
    rw [List.ofFn_succ]
    change θ.matrix (w 0)*product θ (List.ofFn (fun i : Fin n => w i.succ)) = _
    rw [ih]
    rfl

private theorem block_ofFn (t : ℤ) (n : ℕ) (w : Fin n → Bool) :
    block t (List.ofFn w) = visibleCylinder t n w := by
  ext z
  constructor
  · intro h k
    have hh := h ⟨k.val,by simpa using k.isLt⟩
    simpa using hh
  · intro h k
    have hh := h ⟨k.val,by simpa using k.isLt⟩
    simpa using hh

private theorem point_allowed (n : ℕ) (b : Bool) (w : Fin n → Bool)
    (z : ℤ → Bool) (t : ℤ) (hno : ∀ u : ℤ, ¬(z u = true ∧ z (u+1) = true))
    (hw : ∀ k, z (t+k.val) = w k) (hb : b = true → z (t-1) = true) :
    TwelveStatePresentation.Allowed b n w := by
  induction n generalizing b t with
  | zero => trivial
  | succ n ih =>
    constructor
    · rintro ⟨hb',hx⟩
      apply hno (t-1)
      exact ⟨hb hb',by simpa using (hw 0).trans hx⟩
    · apply ih (w 0) (Fin.tail w) (t+1)
      · intro k
        have hh := hw k.succ
        simpa only [Fin.tail,Fin.val_succ,Nat.cast_add,Nat.cast_one,add_assoc,add_left_comm,add_comm] using hh
      · intro hx
        simpa using (hw 0).trans hx

private theorem positive_word_legal (θ : Presentation H) (t : ℤ) (n : ℕ) (w : Fin n → Bool)
    (hw : 0 < (visibleLaw θ : Measure _).real (visibleCylinder t n w)) :
    TwelveStatePresentation.Legal n w := by
  have hno := visible_no11 θ (jointLaw θ : Measure _) (same_law_trimming θ).1
  change (∀ᵐ z ∂(visibleLaw θ : Measure (ℤ → Bool)), ∀ u : ℤ, ¬(z u = true ∧ z (u+1) = true)) at hno
  have hn : (visibleLaw θ : Measure _) (visibleCylinder t n w) ≠ 0 := by
    intro h
    have : (visibleLaw θ : Measure _).real (visibleCylinder t n w) = 0 := by simp [Measure.real,h]
    linarith
  obtain ⟨z,hz,hno⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae hn
    (hno.filter_mono (ae_mono Measure.restrict_le_self))
  exact point_allowed n false w z t hno hz (by simp)

/-- On any stationary finite marked law with full legal support and an exterior-determined
center bit, every positive word is excluded from exact positive rectangular support.
Farther messages and the full-exterior passage are under this same actual law. -/
theorem supported_word_obstruction (θ : Presentation H)
    (hfull : fullMean θ =ᵐ[(visibleLaw θ : Measure (ℤ → Bool))] erasedBit)
    (hsupport : ∀ (t : ℤ) (n : ℕ) (w : Fin n → Bool), TwelveStatePresentation.Legal n w →
      0 < (visibleLaw θ : Measure _).real (visibleCylinder t n w))
    (n : ℕ) (w : Fin n → Bool)
    (hw : 0 < (visibleLaw θ : Measure _).real (visibleCylinder 0 n w)) :
    ¬ Nonempty (Rectangle (wordMatrix θ.matrix n w)) := by
  have hs : ∀ t n w, 0 < (visibleLaw θ : Measure _).real (visibleCylinder t n w) ↔
      TwelveStatePresentation.Legal n w := fun t n w =>
    ⟨positive_word_legal θ t n w,hsupport t n w⟩
  have hx := exclusion θ hfull hs (List.ofFn w) (by rw [block_ofFn]; exact hw)
  rwa [product_ofFn] at hx

/-- Every finite stationary presentation of the same actual twelve-state output law excludes
positive rectangular-support products for every positive-probability word. The arbitrary
farther-message guard is passed to the native full exterior on this very visible law. -/
theorem actual_every_presentation (θ : Presentation H)
    (hsame : visibleLaw θ = TwelveStatePresentation.visible)
    (n : ℕ) (w : Fin n → Bool)
    (hw : 0 < (visibleLaw θ : Measure _).real (visibleCylinder 0 n w)) :
    ¬ Nonempty (Rectangle (wordMatrix θ.matrix n w)) := by
  have hμ : (visibleLaw θ : Measure (ℤ → Bool)) = (TwelveStatePresentation.visible : Measure _) :=
    congrArg (fun p : ProbabilityMeasure (ℤ → Bool) => (p : Measure (ℤ → Bool))) hsame
  have hf : fullMean θ =ᵐ[(visibleLaw θ : Measure (ℤ → Bool))] erasedBit := by
    change bitPredictor (visibleLaw θ : Measure _) (fun z => z 0) exterior ∘ exterior =ᵐ[_] erasedBit
    have ha := TwelveStateFullErasure.actual_full_erasure.1
    change bitPredictor (TwelveStatePresentation.visible : Measure _) (fun z => z 0) exterior ∘ exterior
      =ᵐ[(TwelveStatePresentation.visible : Measure (ℤ → Bool))] erasedBit at ha
    have hp := congrArg (fun p : ProbabilityMeasure (ℤ → Bool) =>
      bitPredictor (p : Measure (ℤ → Bool)) (fun z => z 0) exterior) hsame
    rw [hp]
    rwa [hμ]
  have hs : ∀ t n w, 0 < (visibleLaw θ : Measure _).real (visibleCylinder t n w) ↔
      TwelveStatePresentation.Legal n w := by
    intro t n w
    rw [hμ]
    exact TwelveStatePresentation.actual_visible_support t n w
  exact supported_word_obstruction θ hf (fun t n w hw => (hs t n w).mpr hw) n w hw

theorem irreducible_initial_positive (θ : Presentation H)
    (hirr : ∀ i j : H, ∃ n : ℕ, 0 < ((θ.matrix false+θ.matrix true)^n) i j) :
    ∀ j, 0 < θ.initial j := by
  let A := θ.matrix false+θ.matrix true
  have hn (i j : H) : 0 ≤ A i j := add_nonneg (θ.matrix_nonneg _ _ _) (θ.matrix_nonneg _ _ _)
  have hpow (n : ℕ) (i j : H) : 0 ≤ (A^n) i j := by
    induction n generalizing i with
    | zero => simp [Matrix.one_apply]; split_ifs <;> norm_num
    | succ n ih =>
      rw [pow_succ',Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (hn i k) (ih k)
  have hs : θ.initial ᵥ* A = θ.initial := funext θ.stationary
  have hp (n : ℕ) : θ.initial ᵥ* (A^n) = θ.initial := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,← Matrix.vecMul_vecMul,ih,hs]
  have ht : 0 < ∑ i, θ.initial i := by rw [θ.initial_sum]; norm_num
  obtain ⟨i,_,hi⟩ := (Finset.sum_pos_iff_of_nonneg fun i _ => θ.initial_nonneg i).mp ht
  intro j
  obtain ⟨n,hn⟩ := hirr i j
  have hle : θ.initial i*(A^n) i j ≤ θ.initial j := by
    calc
      _ ≤ ∑ k, θ.initial k*(A^n) k j :=
        Finset.single_le_sum (fun k _ => mul_nonneg (θ.initial_nonneg k) (hpow n k j)) (Finset.mem_univ i)
      _ = θ.initial j := congrFun (hp n) j
  exact (mul_pos hi hn).trans_le hle

private theorem rectangle_word_positive (θ : Presentation H) (hinit : ∀ i, 0 < θ.initial i)
    (n : ℕ) (w : Fin n → Bool) (R : Rectangle (wordMatrix θ.matrix n w)) :
    0 < (visibleLaw θ : Measure _).real (visibleCylinder 0 n w) := by
  obtain ⟨i,hi⟩ := R.rows_nonempty
  obtain ⟨j,hj⟩ := R.cols_nonempty
  have hn (k l : H) : 0 ≤ wordMatrix θ.matrix n w k l := by
    rw [← product_ofFn]
    exact product_nonneg θ _ k l
  have hp : 0 < θ.initial i*wordMatrix θ.matrix n w i j := mul_pos (hinit i) (R.positive i hi j hj)
  have hle : θ.initial i*wordMatrix θ.matrix n w i j ≤
      ∑ k, ∑ l, θ.initial k*wordMatrix θ.matrix n w k l := by
    exact (Finset.single_le_sum (fun l _ => mul_nonneg (θ.initial_nonneg i) (hn i l))
      (Finset.mem_univ j)).trans (Finset.single_le_sum
        (fun k _ => Finset.sum_nonneg fun l _ => mul_nonneg (θ.initial_nonneg k) (hn k l))
          (Finset.mem_univ i))
  have hm := block_mass θ 0 (List.ofFn w)
  rw [block_ofFn,product_ofFn] at hm
  rw [hm]
  exact hp.trans_le hle

/-- Positive irreducible stationary presentations of the actual law have no rectangular word
at all. This includes every finite Condition K arrival-observation presentation, without
needing its additional aperiodicity assumption. -/
theorem actual_irreducible_obstruction (θ : Presentation H)
    (hsame : visibleLaw θ = TwelveStatePresentation.visible)
    (hirr : ∀ i j : H, ∃ n : ℕ, 0 < ((θ.matrix false+θ.matrix true)^n) i j)
    (n : ℕ) (w : Fin n → Bool) :
    ¬ Nonempty (Rectangle (wordMatrix θ.matrix n w)) := by
  rintro ⟨R⟩
  have hp := rectangle_word_positive θ (irreducible_initial_positive θ hirr) n w R
  exact actual_every_presentation θ hsame n w hp ⟨R⟩

private theorem trim_visible_eq (θ : Presentation H) :
    visibleLaw (PositiveSupportPresentation.trim θ) = visibleLaw θ := by
  apply ProbabilityMeasure.toMeasure_injective
  apply TwelveStateGhost.visible_eq_of_cylinders
  intro t n w
  have htrim := (same_law_trimming (PositiveSupportPresentation.trim θ)).2.2.2.2.2.2.2.1 t n w
  have hret := visible_masses (PositiveSupportPresentation.trim θ)
    (retainedLaw θ : Measure _) (same_law_trimming θ).2.1 t n w
  rw [(same_law_trimming θ).2.2.2.1] at hret
  exact htrim.trans hret.symm

/-- Positive-mass trimming preserves the complete visible law. On every alternative
stationary presentation of the actual law, its trimmed matrices exclude all rectangular
word products, including the empty word and with no occurrence premise. -/
theorem actual_trimmed_obstruction (θ : Presentation H)
    (hsame : visibleLaw θ = TwelveStatePresentation.visible) :
    visibleLaw (PositiveSupportPresentation.trim θ) = visibleLaw θ ∧
    ∀ (n : ℕ) (w : Fin n → Bool), ¬ Nonempty (Rectangle
      (wordMatrix (PositiveSupportPresentation.trim θ).matrix n w)) := by
  refine ⟨trim_visible_eq θ,?_⟩
  intro n w
  rintro ⟨R⟩
  have hp := rectangle_word_positive (PositiveSupportPresentation.trim θ) (fun i => i.property) n w R
  exact actual_every_presentation (PositiveSupportPresentation.trim θ)
    ((trim_visible_eq θ).trans hsame) n w hp ⟨R⟩

#print axioms actual_trimmed_obstruction

#print axioms supported_word_obstruction
#print axioms actual_every_presentation
#print axioms actual_irreducible_obstruction

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleLaw
