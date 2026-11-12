/- GID: D5/S3/Quantum/Foundation/FinitePureSimplex
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FinitePureSimplex
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Least coordinate effects on the entire finite-pure original cone. -/

import D5.S3.Quantum.Foundation.FinitePureEffectDescent
import Mathlib.Analysis.Convex.Combination

/-! Weighted relations and comparison on the original finite pure carrier. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Foundation.FinitePureSimplex

open CircuitBalancedConfirmation FinitePureEffectDescent

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]

/-- The whole base is a simplex precisely when its full pure family is affinely
independent; equality with its finite convex hull is included explicitly. -/
def simplex (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) : Prop :=
  AffineIndependent ℝ (fun p : pure C u => (p : A)) ∧
    base C u = convexHull ℝ (pure C u)

open Classical in
/-- For zero relation kernel, the coordinate effects are least against every
original confirmer on the entire cone, not only at other pure vertices. -/
theorem zero_kernel_least_confirmation (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    [Fintype (pure C u)] (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤)
    (hker : LinearMap.ker (coordinates C u) = ⊥) :
    ∃ e : pure C u → (A →ₗ[ℝ] ℝ),
      (∀ p : pure C u, confirms C u p (e p)) ∧
      (∀ p q : pure C u, e p q = if q = p then 1 else 0) ∧
      (∀ (p : pure C u) f, confirms C u p f → ∀ x ∈ C, e p x ≤ f x) ∧
      (∀ (p : pure C u) x, x ∈ C → comparison C u p x = e p x) ∧
      zeroGluing C u := by
  classical
  have hcoeff (w : pure C u → ℝ) (hw : coordinates C u w = 0) : w = 0 := by
    have hm : w ∈ LinearMap.ker (coordinates C u) := hw
    rwa [hker, Submodule.mem_bot] at hm
  have he (p : pure C u) : ∃ f : A →ₗ[ℝ] ℝ,
      proper C u f ∧ ∀ q : pure C u, f q = if q = p then 1 else 0 := by
    have huq := (full_effect_iff C u hclosed hstrict hspan
      (fun q => if q = p then 1 else 0)).mpr (by
      refine ⟨fun q => ?_, fun w hw => ?_⟩
      · split_ifs <;> norm_num
      · rw [hcoeff w hw]
        simp)
    exact ⟨huq.choose,huq.choose_spec.1⟩
  choose e hproper hvalue using he
  have hconf (p : pure C u) : confirms C u p (e p) :=
    ⟨hproper p,by simp [hvalue]⟩
  have hleast (p : pure C u) (f : A →ₗ[ℝ] ℝ) (hf : confirms C u p f) :
      ∀ x ∈ C, e p x ≤ f x := by
    have hh := nonneg_on_cone (f := f-e p) (base_compact hclosed hstrict) hstrict (fun q => ?_)
    · intro x hx
      simpa only [LinearMap.sub_apply,sub_nonneg] using hh x hx
    · by_cases hqp : q = p
      · subst q
        simp [LinearMap.sub_apply,hvalue,hf.2]
      · simpa [LinearMap.sub_apply,hvalue,hqp] using (hf.1 q (pure_mem q).1).1
  have hcomp (p : pure C u) (x : A) (hx : x ∈ C) :
      comparison C u p x = e p x :=
    attained_comparison hx (e p) (hconf p) (fun f hf => hleast p f hf x hx)
  refine ⟨e,hconf,hvalue,hleast,hcomp,?_⟩
  intro p x y hx hy hxe hye
  obtain ⟨fx,hfx,hfx0⟩ := hxe
  obtain ⟨fy,hfy,hfy0⟩ := hye
  have hex : e p x = 0 := le_antisymm (hfx0 ▸ hleast p fx hfx x hx.1)
    (hproper p x hx.1).1
  have hey : e p y = 0 := le_antisymm (hfy0 ▸ hleast p fy hfy y hy.1)
    (hproper p y hy.1).1
  exact ⟨e p,hconf p,by simp [map_smul,map_add,hex,hey]⟩


omit [FiniteDimensional ℝ A] in
private theorem no_single_positive {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    [Fintype (pure C u)] (w : pure C u → ℝ)
    (hw : coordinates C u w = 0) (q : pure C u) (hq : 0 < w q)
    (hother : ∀ i, i ≠ q → w i ≤ 0) : False := by
  classical
  let s := Finset.univ.erase q
  have hmass : (∑ i ∈ s, -w i) = w q := by
    have hz := relation_sum_zero w hw
    have hh := Finset.sum_erase_add (s := Finset.univ) w (Finset.mem_univ q)
    simp only [Finset.sum_neg_distrib]
    dsimp [s]
    linarith
  have hvec : (∑ i ∈ s, (-w i) • (i : A)) = w q • (q : A) := by
    have hh := Finset.sum_erase_add (s := Finset.univ)
      (fun i : pure C u => w i • (i : A)) (Finset.mem_univ q)
    change (∑ i, w i • (i : A)) = 0 at hw
    rw [hw] at hh
    dsimp [s]
    simp only [neg_smul,Finset.sum_neg_distrib]
    exact neg_eq_iff_add_eq_zero.mpr hh
  have hmem : (q : A) ∈ convexHull ℝ (base C u \ {(q : A)}) := by
    have h := s.centerMass_mem_convexHull (s := base C u \ {(q : A)})
      (z := fun i : pure C u => (i : A))
      (fun i hi => neg_nonneg.mpr (hother i (Finset.ne_of_mem_erase hi)))
      (by simpa [hmass] using hq)
      (fun i hi => ⟨pure_mem i,by
        simpa only [Set.mem_singleton_iff,ne_eq,Subtype.coe_inj] using Finset.ne_of_mem_erase hi⟩)
    simpa only [Finset.centerMass,hmass,hvec,inv_smul_smul₀ hq.ne'] using h
  exact ((base_convex C u).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff.mp q.property).2 hmem

private theorem one_relation_obstruction {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    [Fintype (pure C u)] (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤)
    (w : pure C u → ℝ) (hw : coordinates C u w = 0)
    (p : pure C u) (hp : 0 < w p)
    (hmin : ∀ q, w q < 0 → w p ≤ -w q)
    (hfull : ∀ v, coordinates C u v = 0 → ∃ k : ℝ, v = k • w) :
    ¬ zeroGluing C u := by
  classical
  let N := Finset.univ.filter (fun q => w q < 0)
  have hN (q : pure C u) : q ∈ N ↔ w q < 0 := by simp [N]
  have hNne : N.Nonempty := by
    by_contra hn
    have hall : ∀ q, 0 ≤ w q := by
      intro q
      exact le_of_not_gt (fun h => hn ⟨q,(hN q).mpr h⟩)
    have hsum := Finset.single_le_sum (s := Finset.univ) (a := p)
      (fun q _ => hall q) (Finset.mem_univ p)
    rw [relation_sum_zero w hw] at hsum
    linarith
  have hother (q : pure C u) (hq : q ∈ N) : ∃ r, r ∈ N ∧ r ≠ q := by
    by_contra hn
    push Not at hn
    exact no_single_positive (-w) (by simpa using congrArg Neg.neg hw) q
      (neg_pos.mpr ((hN q).mp hq)) (by
        intro r hr
        exact neg_nonpos.mpr (le_of_not_gt (fun h => hr (hn r ((hN r).mpr h)))))
  have hexclude (q : pure C u) (hq : q ∈ N) :
      ∃ f, confirms C u p f ∧ f q = 0 := by
    obtain ⟨r,hr,hrq⟩ := hother q hq
    have hrneg := (hN r).mp hr
    have hpr : p ≠ r := by intro he; subst r; linarith
    let v : pure C u → ℝ := fun z => if z = p then 1 else if z = r then w p / (-w r) else 0
    have hb : ∀ z, 0 ≤ v z ∧ v z ≤ 1 := by
      intro z
      by_cases hzp : z = p
      · simp [v,hzp]
      by_cases hzr : z = r
      · simp only [v,ite_eq_right hzp,ite_eq_left hzr]
        exact ⟨(div_pos hp (neg_pos.mpr hrneg)).le,
          (div_le_one (neg_pos.mpr hrneg)).mpr (hmin r hrneg)⟩
      · simp [v,hzp,hzr]
    have hbal : ∑ z, w z * v z = 0 := by
      have hv : v = fun z => (if z = p then 1 else 0) +
          (if z = r then w p / (-w r) else 0) := by
        ext z
        by_cases hzp : z = p
        · subst z
          simp [v,hpr]
        · simp [v,hzp]
      rw [hv]
      simp only [mul_add,mul_ite,mul_one,mul_zero,Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      field_simp [hrneg.ne]
      ring
    obtain ⟨f,⟨hf,he⟩,_⟩ := (full_effect_iff C u hclosed hstrict hspan v).mpr
      ⟨hb,by intro c hc; obtain ⟨k,rfl⟩ := hfull c hc
             simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum,hbal,mul_zero]⟩
    have hfp : confirms C u p f := ⟨hf,by simpa [v] using he p⟩
    have hqp : q ≠ p := by intro h; subst q; linarith [(hN p).mp hq]
    have hfq : f q = 0 := by simpa [v,hqp,Ne.symm hrq] using he q
    exact ⟨f,hfp,hfq⟩
  let mass := ∑ q ∈ N, -w q
  have hmass : 0 < mass := Finset.sum_pos (fun q hq => neg_pos.mpr ((hN q).mp hq)) hNne
  let z := N.centerMass (fun q => -w q) (fun q : pure C u => (q : A))
  intro hZ
  have hconv : Convex ℝ {x | x ∈ base C u ∧ ∃ f, confirms C u p f ∧ f x = 0} := by
    intro x hx y hy a b ha hb hab
    obtain ⟨f,hf,hfm⟩ := hZ p x y hx.1 hy.1 hx.2 hy.2
    have hfx : f x = 0 := by
      have hnx := (hf.1 x hx.1.1).1
      have hny := (hf.1 y hy.1.1).1
      simp only [map_smul,map_add,smul_eq_mul] at hfm
      linarith
    have hfy : f y = 0 := by
      have hnx := (hf.1 x hx.1.1).1
      have hny := (hf.1 y hy.1.1).1
      simp only [map_smul,map_add,smul_eq_mul] at hfm
      linarith
    exact ⟨base_convex C u hx.1 hy.1 ha hb hab,
      f,hf,by simp [map_add,map_smul,hfx,hfy]⟩
  have hz : z ∈ base C u ∧ ∃ f, confirms C u p f ∧ f z = 0 :=
    hconv.centerMass_mem (fun q hq => (neg_pos.mpr ((hN q).mp hq)).le) hmass
      (fun q hq => ⟨pure_mem q,hexclude q hq⟩)
  have hlower (f : A →ₗ[ℝ] ℝ) (hf : confirms C u p f) : w p / mass ≤ f z := by
    have hrel : ∑ q, w q * f q = 0 := by
      have h := congrArg f hw
      simpa [coordinates,Fintype.linearCombination_apply,map_sum,map_smul,smul_eq_mul] using h
    have hpN : p ∈ Finset.univ \ N := by simp [N,hp.not_gt]
    have hpos : w p ≤ ∑ q ∈ Finset.univ \ N, w q * f q := by
      have hh := Finset.single_le_sum (s := Finset.univ \ N) (a := p) (fun q hq =>
        mul_nonneg (le_of_not_gt (fun h => (Finset.mem_sdiff.mp hq).2 ((hN q).mpr h)))
          (hf.1 q (pure_mem q).1).1) hpN
      simpa [hf.2] using hh
    have hsplit := Finset.sum_sdiff (Finset.subset_univ N) (f := fun q => w q * f q)
    have hn : w p ≤ ∑ q ∈ N, (-w q) * f q := by
      simp only [neg_mul,Finset.sum_neg_distrib]
      linarith
    have hzval : f z = (∑ q ∈ N, (-w q) * f q) / mass := by
      simp [z,Finset.centerMass,map_smul,map_sum,smul_eq_mul,mass,div_eq_inv_mul]
    rw [hzval]
    exact (div_le_div_iff_of_pos_right hmass).mpr hn
  obtain ⟨f,hf,hfz⟩ := hz.2
  have hh := hlower f hf
  rw [hfz] at hh
  exact (not_le_of_gt (div_pos hp hmass)) hh


/-- The original whole-base theorem: for a finite full pure set and relation
nullity at most one, mixed-state zero gluing is equivalent to being a simplex. -/
theorem zero_gluing_iff_simplex (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    [Fintype (pure C u)] (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤)
    (hnullity : Module.finrank ℝ (LinearMap.ker (coordinates C u)) ≤ 1) :
    zeroGluing C u ↔ simplex C u := by
  classical
  have hbase : base C u = convexHull ℝ (pure C u) := by
    have hh := closure_convexHull_extremePoints (base_compact hclosed hstrict) (base_convex C u)
    have hc := (Set.toFinite (pure C u)).isClosed_convexHull (𝕜 := ℝ)
    change closure (convexHull ℝ (pure C u)) = base C u at hh
    rw [hc.closure_eq] at hh
    exact hh.symm
  have hzero : zeroGluing C u → LinearMap.ker (coordinates C u) = ⊥ := by
    intro hZ
    obtain ⟨r,hr⟩ := (finrank_le_one_iff (K := ℝ)).mp hnullity
    by_cases hr0 : r = 0
    · apply le_antisymm ?_ bot_le
      intro w hw
      obtain ⟨k,hk⟩ := hr ⟨w,hw⟩
      have hh := congrArg Subtype.val hk
      simp [hr0] at hh
      simpa only [Submodule.mem_bot] using hh.symm
    have hrne : (r : pure C u → ℝ) ≠ 0 := by
      intro hh
      apply hr0
      exact Subtype.ext hh
    have hsne : (Finset.univ.filter (fun q => r.val q ≠ 0)).Nonempty := by
      obtain ⟨q,hq⟩ := Function.ne_iff.mp hrne
      exact ⟨q,by simpa using hq⟩
    obtain ⟨p,hp,hmin⟩ := Finset.exists_min_image
      (Finset.univ.filter (fun q => r.val q ≠ 0)) (fun q => |r.val q|) hsne
    have hp0 : r.val p ≠ 0 := by simpa using hp
    have hfull (v : pure C u → ℝ) (hv : coordinates C u v = 0) :
        ∃ k : ℝ, v = k • (r : pure C u → ℝ) := by
      obtain ⟨k,hk⟩ := hr ⟨v,hv⟩
      exact ⟨k,(congrArg Subtype.val hk).symm⟩
    exfalso
    rcases lt_or_gt_of_ne hp0 with hpneg | hppos
    · apply one_relation_obstruction hclosed hstrict hspan (-r.val)
        (by simpa using congrArg Neg.neg r.property) p (neg_pos.mpr hpneg) ?_ ?_ hZ
      · intro q hq
        have hqpos : 0 < r.val q := by simpa using hq
        have hh := hmin q (by simp [hqpos.ne'])
        simpa [abs_of_neg hpneg,abs_of_pos hqpos] using hh
      · intro v hv
        obtain ⟨k,hk⟩ := hfull v hv
        exact ⟨-k,by simpa using hk⟩
    · exact one_relation_obstruction hclosed hstrict hspan r.val r.property p hppos
        (fun q hq => by
          have hh := hmin q (by simp [hq.ne])
          simpa [abs_of_pos hppos,abs_of_neg hq] using hh) hfull hZ
  constructor
  · intro hZ
    refine ⟨?_,hbase⟩
    apply LinearIndependent.affineIndependent
    apply (linearIndependent_iff_injective_fintypeLinearCombination).mpr
    exact LinearMap.ker_eq_bot.mp (hzero hZ)
  · intro hS
    have hker : LinearMap.ker (coordinates C u) = ⊥ := by
      apply LinearMap.ker_eq_bot'.mpr
      intro w hw
      have hsum := relation_sum_zero w hw
      have hweighted : Finset.univ.weightedVSub (fun p : pure C u => (p : A)) w = 0 := by
        rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _
          (by simpa using hsum) (0 : A),Finset.weightedVSubOfPoint_apply]
        simpa [coordinates,Fintype.linearCombination_apply] using hw
      ext p
      exact (affineIndependent_iff_of_fintype ℝ _).mp hS.1 w hsum hweighted p
    obtain ⟨e,he,hvalues,hleast,hcomp,hZ⟩ :=
      zero_kernel_least_confirmation C u hclosed hstrict hspan hker
    exact hZ

end D5.S3.Quantum.Foundation.FinitePureSimplex
