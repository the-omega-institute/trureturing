/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleSmoothing
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleSmoothing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original finite-record posteriors forget either exterior through counted rectangular words. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleLaw
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
open Matrix
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleMessages
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleSmoothing
variable {H : Type*} [Fintype H]

private def Bounds (p q : H → ℝ) (l h : ℝ) : Prop :=
  ∀ i, l * q i ≤ p i ∧ p i ≤ h * q i

private def Contracts (T : Matrix H H ℝ) (c : ℝ) : Prop :=
  ∀ (p q : H → ℝ) (l h : ℝ), l ≤ h → (∀ i, 0 ≤ q i) → Bounds p q l h →
  ∃ l' h', l' ≤ h' ∧ h' - l' ≤ c * (h-l) ∧
    (∀ i, 0 ≤ (T *ᵥ q) i) ∧ Bounds (T *ᵥ p) (T *ᵥ q) l' h'

private theorem nonnegative_contracts (T : Matrix H H ℝ) (hT : ∀ i j, 0 ≤ T i j) :
    Contracts T 1 := by
  intro p q l h hlh hq hp
  refine ⟨l,h,hlh,by simp,?_,?_⟩
  · intro i
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hT i j) (hq j)
  · intro i
    constructor
    · simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => by
        nlinarith [mul_le_mul_of_nonneg_left (hp j).1 (hT i j)]
    · simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => by
        nlinarith [mul_le_mul_of_nonneg_left (hp j).2 (hT i j)]

private theorem contracts_mul (T U : Matrix H H ℝ) (c d : ℝ) (hc : 0 ≤ c)
    (hT : Contracts T c) (hU : Contracts U d) : Contracts (T*U) (c*d) := by
  intro p q l h hlh hq hp
  obtain ⟨a,b,hab,hw,hq',hp'⟩ := hU p q l h hlh hq hp
  obtain ⟨a',b',hab',hw',hq'',hp''⟩ := hT (U*ᵥp) (U*ᵥq) a b hab hq' hp'
  refine ⟨a',b',hab',?_,?_,?_⟩
  · exact hw'.trans (by nlinarith [mul_le_mul_of_nonneg_left hw hc])
  · simpa only [Matrix.mulVec_mulVec] using hq''
  · simpa only [Matrix.mulVec_mulVec] using hp''

private theorem rectangle_contracts (B : Matrix H H ℝ) (R : Rectangle B)
    (u v : ℝ) (hu : 0 < u) (huv : u ≤ v)
    (hmin : ∀ i ∈ R.rows, ∀ j ∈ R.cols, u ≤ B i j)
    (hmax : ∀ i ∈ R.rows, ∀ j ∈ R.cols, B i j ≤ v) :
    Contracts B (1-u/v) := by
  have hv : 0 < v := hu.trans_le huv
  have hc : 0 ≤ 1-u/v := sub_nonneg.mpr ((div_le_one hv).mpr huv)
  have hB (i j : H) : 0 ≤ B i j := by
    by_cases hh : i ∈ R.rows ∧ j ∈ R.cols
    · exact (R.positive i hh.1 j hh.2).le
    · rw [R.zero i j hh]
  intro p q l h hlh hq hp
  let S := ∑ j ∈ R.cols, q j
  let P := ∑ j ∈ R.cols, p j
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => hq j
  have restricted (f : H → ℝ) (i : H) :
      (B *ᵥ f) i = ∑ j ∈ R.cols, B i j * f j := by
    apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro j _ hj
    change B i j * f j = 0
    rw [R.zero i j (fun hh => hj hh.2),zero_mul]
  have outside (f : H → ℝ) (i : H) (hi : i ∉ R.rows) : (B *ᵥf) i = 0 := by
    exact Finset.sum_eq_zero fun j _ => by
      change B i j * f j = 0
      rw [R.zero i j (fun hh => hi hh.1),zero_mul]
  have hq' (i : H) : 0 ≤ (B *ᵥ q) i :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hB i j) (hq j)
  by_cases hSp : 0 < S
  · let a := u/v
    let l' := l+a*(P/S-l)
    let h' := h+a*(P/S-h)
    have ha : 0 ≤ a := (div_pos hu hv).le
    have ha1 : a ≤ 1 := (div_le_one hv).mpr huv
    have width : h'-l' = (1-u/v)*(h-l) := by dsimp [h',l',a]; ring
    refine ⟨l',h',by nlinarith [sub_nonneg.mpr hlh],width.le,hq',?_⟩
    intro i
    by_cases hi : i ∈ R.rows
    · have qlo : u*S ≤ (B*ᵥq) i := by
        rw [restricted, Finset.mul_sum]
        exact Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_right (hmin i hi j hj) (hq j)
      have qhi : (B*ᵥq) i ≤ v*S := by
        rw [restricted, Finset.mul_sum]
        exact Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_right (hmax i hi j hj) (hq j)
      have qpos : 0 < (B*ᵥq) i := (mul_pos hu hSp).trans_le qlo
      have E : 0 ≤ P-l*S := by
        have he : P-l*S = ∑ j ∈ R.cols, (p j-l*q j) := by
          dsimp [P,S]; simp only [Finset.sum_sub_distrib,Finset.mul_sum]
        rw [he]
        exact Finset.sum_nonneg fun j _ => sub_nonneg.mpr (hp j).1
      have F : 0 ≤ h*S-P := by
        have he : h*S-P = ∑ j ∈ R.cols, (h*q j-p j) := by
          dsimp [P,S]; simp only [Finset.sum_sub_distrib,Finset.mul_sum]
        rw [he]
        exact Finset.sum_nonneg fun j _ => sub_nonneg.mpr (hp j).2
      have elo : u*(P-l*S) ≤ (B*ᵥp) i-l*(B*ᵥq) i := by
        have he : (B*ᵥp) i-l*(B*ᵥq) i =
            ∑ j ∈ R.cols, B i j*(p j-l*q j) := by
          rw [restricted,restricted]
          simp only [Finset.mul_sum,Finset.sum_sub_distrib,mul_sub]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [he]
        have he' : P-l*S = ∑ j ∈ R.cols, (p j-l*q j) := by
          dsimp [P,S]; simp only [Finset.sum_sub_distrib,Finset.mul_sum]
        rw [he',Finset.mul_sum]
        exact Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_right (hmin i hi j hj) (sub_nonneg.mpr (hp j).1)
      have ehi : u*(h*S-P) ≤ h*(B*ᵥq) i-(B*ᵥp) i := by
        have he : h*(B*ᵥq) i-(B*ᵥp) i =
            ∑ j ∈ R.cols, B i j*(h*q j-p j) := by
          rw [restricted,restricted]
          simp only [Finset.mul_sum,Finset.sum_sub_distrib,mul_sub]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [he]
        have he' : h*S-P = ∑ j ∈ R.cols, (h*q j-p j) := by
          dsimp [P,S]; simp only [Finset.sum_sub_distrib,Finset.mul_sum]
        rw [he',Finset.mul_sum]
        exact Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_right (hmin i hi j hj) (sub_nonneg.mpr (hp j).2)
      have scale : a/S*(B*ᵥq) i ≤ u := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hSp).mpr
        dsimp [a]
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hv).mpr
        nlinarith [mul_le_mul_of_nonneg_left qhi hu.le]
      constructor
      · have he : l'*(B*ᵥq) i = l*(B*ᵥq) i + (a/S*(B*ᵥq) i)*(P-l*S) := by
          dsimp [l']; field_simp <;> ring
        rw [he]
        nlinarith [mul_le_mul_of_nonneg_right scale E]
      · have he : h'*(B*ᵥq) i = h*(B*ᵥq) i - (a/S*(B*ᵥq) i)*(h*S-P) := by
          dsimp [h']; field_simp <;> ring
        rw [he]
        nlinarith [mul_le_mul_of_nonneg_right scale F]
    · rw [outside p i hi, outside q i hi]
      simp
  · have hSz : S = 0 := le_antisymm (le_of_not_gt hSp) hS
    have hz (j : H) (hj : j ∈ R.cols) : q j = 0 := by
      have hle : q j ≤ S := Finset.single_le_sum (fun j _ => hq j) hj
      exact le_antisymm (hSz ▸ hle) (hq j)
    have hpz (j : H) (hj : j ∈ R.cols) : p j = 0 := by
      have hh := hp j
      rw [hz j hj,mul_zero,mul_zero] at hh
      exact le_antisymm hh.2 hh.1
    have hzero (i : H) : (B*ᵥp) i = 0 ∧ (B*ᵥq) i = 0 := by
      rw [restricted,restricted]
      constructor
      · exact Finset.sum_eq_zero fun j hj => by rw [hpz j hj,mul_zero]
      · exact Finset.sum_eq_zero fun j hj => by rw [hz j hj,mul_zero]
    refine ⟨0,0,le_rfl,by nlinarith [mul_nonneg hc (sub_nonneg.mpr hlh)],hq',?_⟩
    intro i
    rw [(hzero i).1,(hzero i).2]
    simp

private theorem normalized_realization (p q α : H → ℝ) (l h : ℝ)
    (hp : Bounds p q l h) (hq : ∀ i, 0 ≤ q i) (hα : ∀ i, 0 ≤ α i)
    (hpos : 0 < α ⬝ᵥ q) :
    ∃ μ : H → ℝ, (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i) = 1 ∧
      (∀ i, q i = 0 → μ i = 0) ∧
      (α ⬝ᵥ p)/(α ⬝ᵥ q) = ∑ i, μ i * (p i/q i) := by
  let μ := fun i => α i*q i/(α ⬝ᵥ q)
  refine ⟨μ,(fun i => div_nonneg (mul_nonneg (hα i) (hq i)) hpos.le),?_,?_,?_⟩
  · simp only [μ,← Finset.sum_div]
    exact div_self hpos.ne'
  · intro i hi
    simp [μ,hi]
  · rw [dotProduct,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : q i = 0
    · have hh := hp i
      rw [hi,mul_zero,mul_zero] at hh
      have he : p i = 0 := le_antisymm hh.2 hh.1
      simp [μ,hi,he]
    · dsimp [μ]
      field_simp

private theorem weighted_interval (p q α : H → ℝ) (l h : ℝ)
    (hp : Bounds p q l h) (hq : ∀ i, 0 ≤ q i) (hα : ∀ i, 0 ≤ α i)
    (hpos : 0 < α ⬝ᵥ q) :
    l ≤ (α ⬝ᵥ p)/(α ⬝ᵥ q) ∧ (α ⬝ᵥ p)/(α ⬝ᵥ q) ≤ h := by
  obtain ⟨μ,hμ,hμsum,hμzero,he⟩ := normalized_realization p q α l h hp hq hα hpos
  rw [he]
  have bounds (i : H) : μ i*l ≤ μ i*(p i/q i) ∧ μ i*(p i/q i) ≤ μ i*h := by
    by_cases hi : 0 < q i
    · exact ⟨mul_le_mul_of_nonneg_left ((le_div_iff₀ hi).mpr (hp i).1) (hμ i),
        mul_le_mul_of_nonneg_left ((div_le_iff₀ hi).mpr (hp i).2) (hμ i)⟩
    · have hz : q i = 0 := le_antisymm (le_of_not_gt hi) (hq i)
      rw [hμzero i hz]
      simp
  constructor
  · calc
      l = ∑ i, μ i*l := by rw [← Finset.sum_mul,hμsum,one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ => (bounds i).1
  · calc
      _ ≤ ∑ i, μ i*h := Finset.sum_le_sum fun i _ => (bounds i).2
      _ = h := by rw [← Finset.sum_mul,hμsum,one_mul]

private theorem contracted_ratio (T : Matrix H H ℝ) (c : ℝ) (hc : Contracts T c)
    (p q α β : H → ℝ) (hq : ∀ i, 0 ≤ q i) (hp : Bounds p q 0 1)
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (ha : 0 < α ⬝ᵥ (T*ᵥq)) (hb : 0 < β ⬝ᵥ (T*ᵥq)) :
    |(α ⬝ᵥ (T*ᵥp))/(α ⬝ᵥ (T*ᵥq)) - (β ⬝ᵥ (T*ᵥp))/(β ⬝ᵥ (T*ᵥq))| ≤ c := by
  obtain ⟨l,h,_,hw,hq',hph⟩ := hc p q 0 1 (by norm_num) hq hp
  have h1 := weighted_interval _ _ α l h hph hq' hα ha
  have h2 := weighted_interval _ _ β l h hph hq' hβ hb
  rw [abs_le]
  constructor <;> nlinarith

/-- Each disjoint block pays once exactly when the complete original word occurs in it. -/
def originalSuccessCount (w : List Bool) (b : ℕ) : ℕ → List Bool → ℕ
  | 0, _ => 0
  | q+1, xs => (if w <:+: xs.take b then 1 else 0) +
      originalSuccessCount w b q (xs.drop b)

section Original
open MeasureTheory
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleLaw
variable [MeasurableSpace H] [MeasurableSingletonClass H]

private theorem word_factor (θ : Presentation H) (xs ys : List Bool) :
    product θ (xs++ys) = product θ xs * product θ ys := by
  simp only [product,List.map_append,List.prod_append]

private theorem occurrence_contracts (θ : Presentation H) (w : List Bool)
    (R : Rectangle (product θ w)) (u v : ℝ) (hu : 0 < u) (huv : u ≤ v)
    (hmin : ∀ i ∈ R.rows, ∀ j ∈ R.cols, u ≤ product θ w i j)
    (hmax : ∀ i ∈ R.rows, ∀ j ∈ R.cols, product θ w i j ≤ v)
    (xs : List Bool) (hx : w <:+: xs) :
    Contracts (product θ xs) (1-u/v) ∧ Contracts (product θ xs)ᵀ (1-u/v) := by
  obtain ⟨a,c,rfl⟩ := hx
  have hρ : 0 ≤ 1-u/v := sub_nonneg.mpr ((div_le_one (hu.trans_le huv)).mpr huv)
  have hf := rectangle_contracts (product θ w) R u v hu huv hmin hmax
  let R' : Rectangle (product θ w)ᵀ := {
    rows := R.cols
    cols := R.rows
    rows_nonempty := R.cols_nonempty
    cols_nonempty := R.rows_nonempty
    positive := fun i hi j hj => R.positive j hj i hi
    zero := fun i j h => R.zero j i (fun h' => h ⟨h'.2,h'.1⟩) }
  have hr := rectangle_contracts (product θ w)ᵀ R' u v hu huv
    (fun i hi j hj => hmin j hj i hi) (fun i hi j hj => hmax j hj i hi)
  have hna := nonnegative_contracts (product θ a) (product_nonneg θ a)
  have hnc := nonnegative_contracts (product θ c) (product_nonneg θ c)
  have hnat := nonnegative_contracts (product θ a)ᵀ (fun i j => product_nonneg θ a j i)
  have hnct := nonnegative_contracts (product θ c)ᵀ (fun i j => product_nonneg θ c j i)
  rw [word_factor,word_factor]
  constructor
  · simpa only [one_mul,mul_one] using
      contracts_mul _ _ _ 1 hρ
        (by simpa only [one_mul] using contracts_mul _ _ 1 _ (by norm_num) hna hf) hnc
  · rw [Matrix.transpose_mul,Matrix.transpose_mul]
    simpa only [one_mul,mul_one] using
      contracts_mul _ _ 1 _ (by norm_num) hnct
        (contracts_mul _ _ _ 1 hρ hr hnat)

private theorem counted_word_contracts (θ : Presentation H) (w : List Bool)
    (R : Rectangle (product θ w)) (u v : ℝ) (hu : 0 < u) (huv : u ≤ v)
    (hmin : ∀ i ∈ R.rows, ∀ j ∈ R.cols, u ≤ product θ w i j)
    (hmax : ∀ i ∈ R.rows, ∀ j ∈ R.cols, product θ w i j ≤ v)
    (b q : ℕ) (xs : List Bool) :
    Contracts (product θ xs) ((1-u/v)^originalSuccessCount w b q xs) ∧
    Contracts (product θ xs)ᵀ ((1-u/v)^originalSuccessCount w b q xs) := by
  have hρ : 0 ≤ 1-u/v := sub_nonneg.mpr ((div_le_one (hu.trans_le huv)).mpr huv)
  induction q generalizing xs with
  | zero =>
    exact ⟨nonnegative_contracts _ (product_nonneg θ xs),
      nonnegative_contracts _ (fun i j => product_nonneg θ xs j i)⟩
  | succ q ih =>
    obtain ⟨hf,hr⟩ := ih (xs.drop b)
    have he : product θ xs = product θ (xs.take b) * product θ (xs.drop b) := by
      rw [← word_factor,List.take_append_drop]
    rw [he,Matrix.transpose_mul]
    by_cases hs : w <:+: xs.take b
    · obtain ⟨hbf,hbr⟩ := occurrence_contracts θ w R u v hu huv hmin hmax (xs.take b) hs
      constructor
      · simpa only [originalSuccessCount,if_pos hs,pow_add,pow_one] using
          contracts_mul _ _ _ _ hρ hbf hf
      · simpa only [originalSuccessCount,if_pos hs,pow_add,pow_one,mul_comm] using
          contracts_mul _ _ _ _ (pow_nonneg hρ _) hr hbr
    · have hbf := nonnegative_contracts _ (product_nonneg θ (xs.take b))
      have hbr := nonnegative_contracts (product θ (xs.take b))ᵀ
        (fun i j => product_nonneg θ (xs.take b) j i)
      constructor
      · simpa only [originalSuccessCount,if_neg hs,zero_add,one_mul] using
          contracts_mul _ _ 1 _ (by norm_num) hbf hf
      · simpa only [originalSuccessCount,if_neg hs,zero_add,mul_one] using
          contracts_mul _ _ _ 1 (pow_nonneg hρ _) hr hbr

/-- The exterior records on their original integer clocks, with the center unobserved. -/
def record (left right : List Bool) : Set (ℤ → Bool) :=
  block (-(left.length:ℤ)) left ∩ block 1 right

/-- The actual center-bit conditional probability on a positive finite record. -/
def recordPosterior (P : Measure (ℤ → Bool)) (left right : List Bool) : ℝ :=
  P.real (record left right ∩ {z | z 0 = true}) / P.real (record left right)

private theorem original_block_mass (θ : Presentation H) (J : Measure (PathSpace H))
    [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ) (t : ℤ) (xs : List Bool) :
    (J.map Prod.snd).real (block t xs) =
      θ.initial ⬝ᵥ (product θ xs *ᵥ fun _ => 1) := by
  have hh := visible_masses θ J hc t xs.length xs.get
  change (J.map Prod.snd).real (block t xs) = _ at hh
  rw [hh]
  simp only [futureMass,← product_word,Matrix.mulVec,dotProduct,mul_one]

private theorem record_bit_mass (θ : Presentation H) (J : Measure (PathSpace H))
    [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ)
    (left right : List Bool) (x : Bool) :
    (J.map Prod.snd).real (record left right ∩ {z | z 0 = x}) =
      θ.initial ⬝ᵥ (product θ left *ᵥ (θ.matrix x *ᵥ (product θ right *ᵥ fun _ => 1))) := by
  have he : block (-(left.length:ℤ)) (left++[x]++right) =
      record left right ∩ {z | z 0 = x} := by
    rw [block_append,block_append]
    ext z
    simp [record,block,Set.mem_inter_iff,and_assoc,and_comm]
  rw [← he,original_block_mass θ J hc,word_factor,word_factor]
  simp only [product,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,Matrix.mul_one,
    Matrix.mulVec_mulVec,Matrix.mul_assoc]

private theorem record_total_mass (θ : Presentation H) (J : Measure (PathSpace H))
    [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ) (left right : List Bool) :
    (J.map Prod.snd).real (record left right) =
      θ.initial ⬝ᵥ (product θ left *ᵥ
        ((θ.matrix false + θ.matrix true) *ᵥ (product θ right *ᵥ fun _ => 1))) := by
  let P := J.map Prod.snd
  have he : record left right = (record left right ∩ {z | z 0 = false}) ∪
      (record left right ∩ {z | z 0 = true}) := by
    ext z
    cases hz : z 0 <;> simp [hz]
  have hmblock (t : ℤ) (xs : List Bool) : MeasurableSet (block t xs) := by
    simp only [block,Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => (measurableSet_singleton (xs.get k)).preimage
      (measurable_pi_apply (t+k.val))
  have hm : MeasurableSet (record left right ∩ {z | z 0 = true}) :=
    ((hmblock _ left).inter (hmblock _ right)).inter
      ((measurableSet_singleton true).preimage (measurable_pi_apply (0:ℤ)))
  rw [he,measureReal_union (by
    apply Set.disjoint_left.mpr
    rintro z ⟨_,hf⟩ ⟨_,ht⟩
    exact Bool.false_ne_true (hf.symm.trans ht)) hm,
    record_bit_mass θ J hc,record_bit_mass θ J hc]
  simp only [Matrix.add_mulVec,Matrix.mulVec_add, dotProduct_add]

private theorem posterior_matrix (θ : Presentation H) (J : Measure (PathSpace H))
    [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ) (left right : List Bool) :
    recordPosterior (J.map Prod.snd) left right =
      (θ.initial ⬝ᵥ (product θ left *ᵥ (θ.matrix true *ᵥ (product θ right *ᵥ fun _ => 1)))) /
      (θ.initial ⬝ᵥ (product θ left *ᵥ
        ((θ.matrix false+θ.matrix true) *ᵥ (product θ right *ᵥ fun _ => 1)))) := by
  rw [recordPosterior,record_bit_mass θ J hc,record_total_mass θ J hc]

/-- The exact minimum of the original word entries on its support rectangle. -/
def rectangleMinimum (B : Matrix H H ℝ) (R : Rectangle B) : ℝ :=
  ((R.rows ×ˢ R.cols).image fun ij => B ij.1 ij.2).min'
    ((R.rows_nonempty.product R.cols_nonempty).image _)

/-- The exact maximum on the same support. -/
def rectangleMaximum (B : Matrix H H ℝ) (R : Rectangle B) : ℝ :=
  ((R.rows ×ˢ R.cols).image fun ij => B ij.1 ij.2).max'
    ((R.rows_nonempty.product R.cols_nonempty).image _)

private theorem extrema (B : Matrix H H ℝ) (R : Rectangle B) :
    0 < rectangleMinimum B R ∧ rectangleMinimum B R ≤ rectangleMaximum B R ∧
    (∀ i ∈ R.rows, ∀ j ∈ R.cols, rectangleMinimum B R ≤ B i j) ∧
    (∀ i ∈ R.rows, ∀ j ∈ R.cols, B i j ≤ rectangleMaximum B R) := by
  have hmin (i : H) (hi : i ∈ R.rows) (j : H) (hj : j ∈ R.cols) :
      rectangleMinimum B R ≤ B i j := by
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_product.mpr ⟨hi,hj⟩,rfl⟩)
  have hmax (i : H) (hi : i ∈ R.rows) (j : H) (hj : j ∈ R.cols) :
      B i j ≤ rectangleMaximum B R := by
    exact Finset.le_max' ((R.rows ×ˢ R.cols).image fun ij => B ij.1 ij.2) _
      (Finset.mem_image.mpr ⟨(i,j),Finset.mem_product.mpr ⟨hi,hj⟩,rfl⟩)
  have hp : 0 < rectangleMinimum B R := by
    obtain ⟨ij,hij,he⟩ := Finset.mem_image.mp (Finset.min'_mem
      ((R.rows ×ˢ R.cols).image fun ij => B ij.1 ij.2)
      ((R.rows_nonempty.product R.cols_nonempty).image _))
    rw [rectangleMinimum,← he]
    exact R.positive ij.1 (Finset.mem_product.mp hij).1 ij.2 (Finset.mem_product.mp hij).2
  obtain ⟨i,hi⟩ := R.rows_nonempty
  obtain ⟨j,hj⟩ := R.cols_nonempty
  exact ⟨hp,(hmin i hi j hj).trans (hmax i hi j hj),hmin,hmax⟩

/-- For every original-cylinder law, the two actual positive finite-record posteriors
satisfy the counted-word bound in both directions. Every count uses disjoint original-clock
blocks, with the left blocks ending at -1 and the right blocks starting at 1. -/
theorem finite_record_smoothing_by_original_success_count
    (θ : Presentation H) (J : Measure (PathSpace H)) [IsProbabilityMeasure J]
    (hc : HasOriginalCylinders J θ) (w : List Bool) (_hw : w ≠ [])
    (R : Rectangle (product θ w)) :
    let b := w.length + Fintype.card H
    let ρ := 1-rectangleMinimum (product θ w) R / rectangleMaximum (product θ w) R
    (∀ (extra left right : List Bool),
      0 < (J.map Prod.snd).real (record (extra++left) right) →
      0 < (J.map Prod.snd).real (record left right) →
      |recordPosterior (J.map Prod.snd) (extra++left) right -
        recordPosterior (J.map Prod.snd) left right| ≤
      ρ ^ originalSuccessCount w b (left.length/b) (left.drop (left.length%b))) ∧
    (∀ (left right extra : List Bool),
      0 < (J.map Prod.snd).real (record left (right++extra)) →
      0 < (J.map Prod.snd).real (record left right) →
      |recordPosterior (J.map Prod.snd) left (right++extra) -
        recordPosterior (J.map Prod.snd) left right| ≤
      ρ ^ originalSuccessCount w b (right.length/b) right) := by
  dsimp only
  let b := w.length + Fintype.card H
  let u := rectangleMinimum (product θ w) R
  let v := rectangleMaximum (product θ w) R
  obtain ⟨hu,huv,hmin,hmax⟩ := extrema (product θ w) R
  have hρ : 0 ≤ 1-u/v := sub_nonneg.mpr ((div_le_one (hu.trans_le huv)).mpr huv)
  have hmv (T : Matrix H H ℝ) (hn : ∀ i j, 0 ≤ T i j) (q : H → ℝ)
      (hq : ∀ i, 0 ≤ q i) (i : H) : 0 ≤ (T*ᵥq) i :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hn i j) (hq j)
  have hvM (α : H → ℝ) (hα : ∀ i, 0 ≤ α i) (T : Matrix H H ℝ)
      (hn : ∀ i j, 0 ≤ T i j) (i : H) : 0 ≤ (α ᵥ*T) i :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hα j) (hn j i)
  have hA (i j : H) : 0 ≤ (θ.matrix false+θ.matrix true) i j :=
    add_nonneg (θ.matrix_nonneg false i j) (θ.matrix_nonneg true i j)
  constructor
  · intro extra left right hlong hshort
    let y := product θ right *ᵥ fun _ => (1:ℝ)
    let p := θ.matrix true *ᵥ y
    let q := (θ.matrix false+θ.matrix true)*ᵥy
    have hy : ∀ i, 0 ≤ y i := hmv _ (product_nonneg θ right) _ (fun _ => by norm_num)
    have hq : ∀ i, 0 ≤ q i := hmv _ hA y hy
    have hp : Bounds p q 0 1 := by
      intro i
      dsimp [p,q]
      simp only [zero_mul,one_mul,Matrix.add_mulVec,Pi.add_apply]
      exact ⟨hmv _ (θ.matrix_nonneg true) y hy i,
        le_add_of_nonneg_left (hmv _ (θ.matrix_nonneg false) y hy i)⟩
    let α := θ.initial ᵥ* product θ extra
    have hα : ∀ i, 0 ≤ α i := hvM _ θ.initial_nonneg _ (product_nonneg θ extra)
    have hm : Contracts (product θ left)
        ((1-u/v)^originalSuccessCount w b (left.length/b) (left.drop (left.length%b))) := by
      have hh := (counted_word_contracts θ w R u v hu huv hmin hmax b
        (left.length/b) (left.drop (left.length%b))).1
      have hn := nonnegative_contracts _ (product_nonneg θ (left.take (left.length%b)))
      have he : product θ left = product θ (left.take (left.length%b)) *
          product θ (left.drop (left.length%b)) := by
        rw [← word_factor,List.take_append_drop]
      rw [he]
      simpa only [one_mul] using contracts_mul _ _ 1 _ (by norm_num) hn hh
    have ha : 0 < α ⬝ᵥ (product θ left*ᵥq) := by
      rw [record_total_mass θ J hc,word_factor,← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec] at hlong
      exact hlong
    have hb : 0 < θ.initial ⬝ᵥ (product θ left*ᵥq) := by
      rw [record_total_mass θ J hc] at hshort
      exact hshort
    have hh := contracted_ratio (product θ left) _ hm p q α θ.initial hq hp
      hα θ.initial_nonneg ha hb
    rw [posterior_matrix θ J hc,posterior_matrix θ J hc,word_factor]
    simpa only [Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul,Matrix.mul_assoc,α,p,q,y] using hh
  · intro left right extra hlong hshort
    let α := θ.initial ᵥ* product θ left
    let p := α ᵥ* θ.matrix true
    let q := α ᵥ* (θ.matrix false+θ.matrix true)
    let β := product θ extra *ᵥ fun _ => (1:ℝ)
    have hα : ∀ i, 0 ≤ α i := hvM _ θ.initial_nonneg _ (product_nonneg θ left)
    have hq : ∀ i, 0 ≤ q i := hvM α hα _ hA
    have hp : Bounds p q 0 1 := by
      intro i
      dsimp [p,q]
      simp only [zero_mul,one_mul,Matrix.vecMul_add,Pi.add_apply]
      exact ⟨hvM α hα _ (θ.matrix_nonneg true) i,
        le_add_of_nonneg_left (hvM α hα _ (θ.matrix_nonneg false) i)⟩
    have hβ : ∀ i, 0 ≤ β i := hmv _ (product_nonneg θ extra) _ (fun _ => by norm_num)
    have hm := (counted_word_contracts θ w R u v hu huv hmin hmax b
      (right.length/b) right).2
    have hre (a β : H → ℝ) : β ⬝ᵥ ((product θ right)ᵀ*ᵥa) =
        a ⬝ᵥ (product θ right *ᵥβ) := by
      rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,dotProduct_comm]
    have ha : 0 < β ⬝ᵥ ((product θ right)ᵀ*ᵥq) := by
      rw [hre]
      rw [record_total_mass θ J hc,word_factor,← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec,Matrix.dotProduct_mulVec] at hlong
      exact hlong
    have hb : 0 < (fun _ => (1:ℝ)) ⬝ᵥ ((product θ right)ᵀ*ᵥq) := by
      rw [hre]
      rw [record_total_mass θ J hc,Matrix.dotProduct_mulVec,Matrix.dotProduct_mulVec] at hshort
      exact hshort
    have hh := contracted_ratio (product θ right)ᵀ _ hm p q β (fun _ => 1) hq hp
      hβ (fun _ => by norm_num) ha hb
    simp only [hre] at hh
    rw [posterior_matrix θ J hc,posterior_matrix θ J hc,word_factor]
    simpa only [Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul,Matrix.mul_assoc,α,p,q,β] using hh

#print axioms finite_record_smoothing_by_original_success_count
end Original
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleSmoothing
