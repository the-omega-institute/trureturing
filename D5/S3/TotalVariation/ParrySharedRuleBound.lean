/- GID: D5/S3/TotalVariation/ParrySharedRuleBound
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParrySharedRuleBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Exp]
   utility: none
   digest: The original shared longest-zero-run rule has a uniform stationary defect bound. -/

import D5.S3.TotalVariation.SharedZeroBoundaryInclusion
import D5.S3.TotalVariation.ParryBoundaryCylinderBound
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Ring.Pow

open scoped BigOperators
open D5.S3.ObserverMemory.Trajectories.LongestZeroSelectorResponse
open D5.S3.ObserverMemory.Trajectories.ZeroRunWordGeometry
open D5.S3.TotalVariation.TwistedResetPaths
open D5.S3.TotalVariation.TwistedPrefixComparison
open D5.S3.TotalVariation.ParryResetLaw
open D5.S3.TotalVariation.ParryWordCollision
open D5.S3.TotalVariation.ParryTwistedComparison
open D5.S3.TotalVariation.ParrySharedZeroRule
open D5.S3.TotalVariation.ParryBoundaryCylinderBound
open D5.S3.TotalVariation.SharedZeroBoundaryInclusion

namespace D5.S3.TotalVariation.ParrySharedRuleBound

set_option autoImplicit false

/-- The identical rule for every source parameter uses latest-closing ties and
strict subsequent transport. Both estimates concern all actual signed prefixes. -/
theorem parry_shared_rule_bound (k : ℕ) (hk : 2 ≤ k) (R : ℕ) (hR : 1 ≤ R) :
    stationaryDefect k R (sharedRule R) ≤ min 1 (512 / (R : ℝ)) ∧
    (18 ≤ R → stationaryDefect k R (sharedRule R) ≤
      4 / (((R - 2) / 16 : ℕ) : ℝ) +
        2 * Real.exp (-((R : ℝ) - 2) / 16) + (31/32 : ℝ)^(R/4)) := by
  classical
  let p := parryParameter k
  let q := 1 - p
  obtain ⟨hr, _, _, hQ, hrow, hπ, hπsum, hstat, _⟩ := parry_stationary_law k hk
  have hp : 0 < p := by dsimp [p]; linarith only [hr.1]
  have hp1 : p < 1 := lt_of_le_of_lt hr.2.1
    (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
  have hp2 : p ≤ 2/3 := by
    have hs : p + p^2 ≤ 1 := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
        (fun i _ _ => pow_nonneg hp.le (i+1))
      change (∑ i ∈ Finset.range 2, p^(i+1)) ≤ rootSum k p at h
      rw [hr.2.2] at h
      simpa [Finset.sum_range_succ] using h
    nlinarith only [hs,hp]
  have hq : 0 < q := sub_pos.mpr hp1
  have hgeom (x : ℝ) (m : ℕ) :
      (∑ i ∈ Finset.Icc 1 m, x^i) * (1-x) = x * (1-x^m) := by
    have h := geom_sum_Ico_mul_neg x (show 1 ≤ m+1 by omega)
    rw [show Finset.Ico 1 (m+1) = Finset.Icc 1 m by
      ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega, pow_one, pow_succ] at h
    nlinarith only [h]
  have hW : (∑ w ∈ Finset.Ico 1 k, p^w) = q/p := by
    have hs : (∑ w ∈ Finset.Ico 1 k, p^w) * p = q := by
      have he : (∑ i ∈ Finset.range k, p^(i+1)) =
          p + ∑ w ∈ Finset.Ico 1 k, p^(w+1) := by
        rw [← Finset.sum_range_add_sum_Ico _ (by omega : 1 ≤ k)]
        simp
      have hr' : (∑ i ∈ Finset.range k, p^(i+1)) = 1 := hr.2.2
      rw [he] at hr'
      simp_rw [pow_succ, ← Finset.sum_mul] at hr'
      dsimp [q]
      linarith only [hr']
    exact (eq_div_iff hp.ne').mpr hs
  have hqident : q^2 = p^2 * (1-p^(k-1)) := by
    have hg := hgeom p (k-1)
    rw [show Finset.Icc 1 (k-1) = Finset.Ico 1 k by
      ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega, hW] at hg
    have hpq : q/p*p = q := div_mul_cancel₀ q hp.ne'
    dsimp [q] at *
    nlinarith only [hg,hpq]
  let size (cs : List (ℕ × ℕ)) := (cs.map (fun c => c.1+c.2)).sum
  let D (m B : ℕ) : Finset (List (ℕ × ℕ)) :=
    (Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 B ×ˢ Finset.Ico 1 k)).image List.ofFn
  have hmemD (m B : ℕ) (cs : List (ℕ × ℕ)) :
      cs ∈ D m B ↔ cs.length = m ∧
        ∀ c ∈ cs, 1 ≤ c.1 ∧ c.1 ≤ B ∧ 1 ≤ c.2 ∧ c.2 < k := by
    constructor
    · intro hc
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hc
      refine ⟨List.length_ofFn, ?_⟩
      intro c hc
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
      simpa only [Finset.mem_product, Finset.mem_Icc, Finset.mem_Ico, and_assoc] using
        Fintype.mem_piFinset.mp hf i
    · rintro ⟨rfl, hc⟩
      refine Finset.mem_image.mpr ⟨cs.get, ?_, List.ofFn_get cs⟩
      apply Fintype.mem_piFinset.mpr
      intro i
      simpa only [Finset.mem_product, Finset.mem_Icc, Finset.mem_Ico, and_assoc] using
        hc (cs.get i) (List.get_mem cs i)
  have hsumD (m B : ℕ) (x : ℝ) :
      (∑ cs ∈ D m B, x^(size cs)) =
        ((∑ z ∈ Finset.Icc 1 B, x^z) * (∑ w ∈ Finset.Ico 1 k, x^w))^m := by
    dsimp only [D]
    rw [Finset.sum_image (fun _ _ _ _ h => List.ofFn_injective h)]
    simp only [size, List.map_ofFn, List.sum_ofFn]
    simp_rw [← Finset.prod_pow_eq_pow_sum]
    simp only [Function.comp_apply]
    rw [Finset.sum_prod_piFinset _ (fun (_ : Fin m) (c : ℕ × ℕ) => x^(c.1+c.2))]
    simp only [Finset.sum_product, pow_add, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hmassD (m B : ℕ) : (∑ cs ∈ D m B, p^(size cs)) = (1-p^B)^m := by
    rw [hsumD, hW]
    congr 1
    have hg := hgeom p B
    apply (mul_right_cancel₀ hp.ne')
    rw [mul_assoc, div_mul_cancel₀ _ hp.ne']
    dsimp [q]
    nlinarith only [hg]
  have hmoment (m B : ℕ) : (∑ cs ∈ D m B, (p*(6/5:ℝ))^(size cs)) ≤ 4^m := by
    let a : ℝ := 6/5
    let x := p*a
    have hx : 0 < x := mul_pos hp (by norm_num [a])
    have hx1 : x < 1 := by dsimp [x,a]; linarith only [hp2]
    have hxd : 0 < 1-x := sub_pos.mpr hx1
    have hz : (∑ z ∈ Finset.Icc 1 B, x^z) ≤ x/(1-x) := by
      apply (le_div_iff₀ hxd).mpr
      rw [hgeom]
      nlinarith only [pow_nonneg hx.le B,hx]
    have hw : (∑ w ∈ Finset.Ico 1 k, x^w) ≤ q^2*a/(p*(1-x)) := by
      apply (le_div_iff₀ (mul_pos hp hxd)).mpr
      have hg := hgeom x (k-1)
      rw [show Finset.Icc 1 (k-1) = Finset.Ico 1 k by
        ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega] at hg
      have hpx : p ≤ x := by dsimp [x,a]; linarith only [hp]
      have hpw := pow_le_pow_left₀ hp.le hpx (k-1)
      have hxid : p*x = p^2*a := by dsimp [x]; ring
      have hh : p*x*(1-x^(k-1)) ≤ p*x*(1-p^(k-1)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hpw]) (mul_nonneg hp.le hx.le)
      have he : p*x*(1-p^(k-1)) = q^2*a := by rw [hqident, hxid]; ring
      rw [he] at hh
      have hgp := congrArg (fun y : ℝ => p*y) hg
      nlinarith only [hh,hgp]
    have hb : q*a/(1-x) ≤ 2 := by
      apply (div_le_iff₀ hxd).mpr
      dsimp [q,x,a]
      linarith only [hp2]
    have hnon : 0 ≤ q*a/(1-x) := by positivity
    rw [hsumD]
    apply pow_le_pow_left₀ (mul_nonneg
      (Finset.sum_nonneg fun _ _ => pow_nonneg hx.le _)
      (Finset.sum_nonneg fun _ _ => pow_nonneg hx.le _))
    calc
      _ ≤ (x/(1-x)) * (q^2*a/(p*(1-x))) :=
        mul_le_mul hz hw (Finset.sum_nonneg fun _ _ => pow_nonneg hx.le _)
          (by positivity)
      _ = (q*a/(1-x))^2 := by dsimp [x]; field_simp
      _ ≤ 4 := by nlinarith only [hb,hnon]
  have hconsD (m B : ℕ) (F : List (ℕ × ℕ) → ℝ) :
      (∑ cs ∈ D (m+1) B, F cs) =
        ∑ c ∈ Finset.Icc 1 B ×ˢ Finset.Ico 1 k, ∑ ds ∈ D m B, F (c::ds) := by
    have he : D (m+1) B =
        ((Finset.Icc 1 B ×ˢ Finset.Ico 1 k) ×ˢ D m B).image
          (fun cd => cd.1 :: cd.2) := by
      ext cs
      constructor
      · intro hc
        obtain ⟨hl,hv⟩ := (hmemD (m+1) B cs).mp hc
        cases cs with
        | nil => simp at hl
        | cons c cs =>
          have hcv := hv c (by simp)
          refine Finset.mem_image.mpr ⟨(c,cs), Finset.mem_product.mpr ⟨?_,?_⟩,rfl⟩
          · simpa only [Finset.mem_product, Finset.mem_Icc, Finset.mem_Ico, and_assoc] using hcv
          · apply (hmemD m B cs).mpr
            exact ⟨by simpa using hl, fun d hd => hv d (by simp [hd])⟩
      · intro hc
        obtain ⟨⟨c,cs⟩,hcs,rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨hc,hs⟩ := Finset.mem_product.mp hcs
        obtain ⟨hl,hv⟩ := (hmemD m B cs).mp hs
        apply (hmemD (m+1) B (c::cs)).mpr
        refine ⟨by simp [hl], ?_⟩
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · simpa only [Finset.mem_product, Finset.mem_Icc, Finset.mem_Ico, and_assoc] using hc
        · exact hv d hd
    rw [he, Finset.sum_image, Finset.sum_product]
    intro a _ b _ hab
    exact Prod.ext (List.cons.inj hab).1 (List.cons.inj hab).2
  let maximal (cs : List (ℕ × ℕ)) := ∀ c ∈ cs, c.1 ≤ (cs.headD (0,0)).1
  have hmaxD (m B : ℕ) :
      (∑ cs ∈ (D (m+1) B).filter maximal, p^(size cs)) ≤ 1/(p*(m+1)) := by
    have hsum : (∑ cs ∈ (D (m+1) B).filter maximal, p^(size cs)) =
        ∑ z ∈ Finset.Icc 1 B, q*p^(z-1)*(1-p^z)^m := by
      rw [Finset.sum_filter, hconsD, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro z hz
      have hz1 := (Finset.mem_Icc.mp hz).1
      have hzB := (Finset.mem_Icc.mp hz).2
      have htail : (D m B).filter (fun ds => ∀ c ∈ ds, c.1 ≤ z) = D m z := by
        ext ds
        simp only [Finset.mem_filter, hmemD]
        constructor
        · rintro ⟨⟨hl, hv⟩, hz⟩
          exact ⟨hl, fun c hc => ⟨(hv c hc).1, hz c hc, (hv c hc).2.2⟩⟩
        · rintro ⟨hl, hv⟩
          exact ⟨⟨hl, fun c hc => ⟨(hv c hc).1, ((hv c hc).2.1).trans hzB,
            (hv c hc).2.2⟩⟩, fun c hc => (hv c hc).2.1⟩
      have he (w : ℕ) :
          (∑ ds ∈ D m B, if maximal ((z,w)::ds) then p^(size ((z,w)::ds)) else 0) =
            p^(z+w)*(1-p^z)^m := by
        simp only [maximal, List.mem_cons, forall_eq_or_imp, List.headD_cons,
          le_refl, true_and, size, List.map_cons, List.sum_cons, pow_add]
        simp_rw [← mul_ite_zero]
        rw [← Finset.mul_sum]
        change (p^z*p^w) * (∑ ds ∈ D m B, if (∀ c ∈ ds, c.1 ≤ z)
          then p^(size ds) else 0) = _
        rw [← Finset.sum_filter, htail, hmassD]
      calc
        _ = ∑ w ∈ Finset.Ico 1 k, p^(z+w)*(1-p^z)^m := by
          apply Finset.sum_congr rfl
          intro w _
          exact he w
        _ = q*p^(z-1)*(1-p^z)^m := by
          simp_rw [pow_add, ← Finset.sum_mul, ← Finset.mul_sum, hW]
          have hpz : p^z = p^(z-1)*p := by rw [← pow_succ]; congr 1; omega
          rw [hpz]
          field_simp
    rw [hsum]
    have hshift : (∑ z ∈ Finset.Icc 1 B, q*p^(z-1)*(1-p^z)^m) =
        ∑ j ∈ Finset.range B, q*p^j*(1-p^(j+1))^m := by
      apply Finset.sum_bij (fun j _ => j-1)
      · intro z hz; simp only [Finset.mem_Icc] at hz; simp; omega
      · intro a ha b hb hab
        simp only [Finset.mem_Icc] at ha hb
        omega
      · intro j hj
        refine ⟨j+1, ?_, by omega⟩
        simp only [Finset.mem_Icc, Finset.mem_range] at *
        omega
      · intro z hz
        have hz1 := (Finset.mem_Icc.mp hz).1
        simp [show z-1+1=z by omega]
    rw [hshift]
    let a : ℕ → ℝ := fun j => 1-p^(j+1)
    have ha (j : ℕ) : 0 ≤ a j := sub_nonneg.mpr (pow_le_one₀ hp.le hp1.le)
    have hd (j : ℕ) : a (j+1)-a j = p*(q*p^j) := by
      dsimp [a,q]; simp only [pow_succ]; ring
    have hstep (j : ℕ) :
        (p*(m+1))*(q*p^j*a j^m) ≤ a (j+1)^(m+1)-a j^(m+1) := by
      have hdn : 0 ≤ a (j+1)-a j := by rw [hd]; positivity
      have h := pow_add_mul_le_add_pow (ha j)
        (show 0 ≤ 2*a j+(a (j+1)-a j) by linarith only [ha j,hdn]) (m+1)
      rw [add_sub_cancel, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, hd] at h
      nlinarith only [h]
    apply (le_div_iff₀ (mul_pos hp (by positivity))).mpr
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range B) => hstep j)
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun j => a j^(m+1)) B] at hh
    have ht : a B^(m+1) ≤ 1 :=
      pow_le_one₀ (ha B) (sub_le_self _ (pow_nonneg hp.le _))
    have hb : 0 ≤ a 0^(m+1) := pow_nonneg (ha 0) _
    dsimp only [a] at hh ht hb
    nlinarith only [hh,ht,hb]
  have hw : ∀ (m : ℕ) (s : State k) (v : Fin m → State k),
      0 ≤ pathWeight k p m s v := by
    intro m
    induction m with
    | zero => intro s v; exact zero_le_one
    | succ m ih => intro s v; exact mul_nonneg (hQ _ _) (ih _ _)
  have hrows : ∀ (m : ℕ) (s : State k),
      (∑ v : Fin m → State k, pathWeight k p m s v) = 1 := by
    intro m
    induction m with
    | zero => intro s; simp [pathWeight]
    | succ m ih =>
      intro s
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (m+1) => State k),
        Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, pathWeight, Fin.cons_zero, Fin.cons_succ]
      simp_rw [← Finset.mul_sum, ih, mul_one]
      exact hrow s
  have hprob (m : ℕ) : (∑ v : Prefix k m, referenceLaw k p m (parryLaw k) v) = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [referenceLaw]
    simp_rw [← Finset.mul_sum, hrows, mul_one]
    exact hπsum
  have hpos (m : ℕ) (v : Prefix k m) : 0 ≤ referenceLaw k p m (parryLaw k) v :=
    mul_nonneg (hπ _) (hw _ _ _)
  have hmassle (w : List Bool) : 0 ≤ stationaryWordMass k w ∧ stationaryWordMass k w ≤ 1 := by
    constructor
    · exact Finset.sum_nonneg (fun _ _ => hpos _ _)
    · rw [← hprob w.length]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => hpos _ _)
  have hone : stationaryDefect k R (sharedRule R) ≤ 1 := by
    rw [← hprob (R+1)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => hpos _ _)
  have hpath : ∀ (a : ℕ) (v : Fin (a+1) → State k),
      pathWeight k p a (v 0) (Fin.tail v) =
        ∏ i : Fin a, kernel k p (v i.castSucc) (v i.succ) ∧
      endpoint a (v 0) (Fin.tail v) = v (Fin.last a) := by
    intro a
    induction a with
    | zero => intro v; simp [pathWeight,endpoint]
    | succ a ih =>
      intro v
      obtain ⟨hw,he⟩ := ih (Fin.tail v)
      constructor
      · simpa +unfoldPartialApp only [pathWeight, Fin.tail, Fin.prod_univ_succ,
          Fin.succ_zero_eq_one, Fin.castSucc_zero, Fin.castSucc_succ] using congrArg
            (fun x => kernel k p (v 0) (v 1) * x) hw
      · simpa +unfoldPartialApp only [endpoint, Fin.tail, Fin.succ_zero_eq_one,
          Fin.succ_last] using he
  have hsnoc (a : ℕ) (s t : State k) (v : Fin a → State k) :
      pathWeight k p (a+1) s (Fin.snoc v t) =
        pathWeight k p a s v * kernel k p (endpoint a s v) t := by
    have h₁ := hpath (a+1) (Fin.cons s (Fin.snoc v t))
    have h₂ := hpath a (Fin.cons s v)
    simp only [Fin.tail_cons, Fin.cons_zero] at h₁ h₂
    rw [h₁.1, Fin.prod_univ_castSucc, h₂.1, h₂.2]
    simp only [Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc, Fin.snoc_last,
      ← Fin.castSucc_succ, Fin.succ_last]
  have hold (F : (Fin R → Bool) → ℝ) :
      (∑ v : Prefix k (R+1), referenceLaw k p (R+1) (parryLaw k) v *
        F (fun i : Fin R => prefixRelation v i.castSucc)) =
      ∑ v : Prefix k R, referenceLaw k p R (parryLaw k) v * F (relations v.1 v.2) := by
    have hrel (s t : State k) (v : Fin R → State k) :
        (fun i : Fin R => prefixRelation (s,Fin.snoc v t) i.castSucc) = relations s v := by
      funext i
      simp only [prefixRelation, relations, Fin.cons_snoc_eq_snoc_cons,
        ← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.cons_succ]
    conv_lhs => rw [Fintype.sum_prod_type]
    conv_rhs => rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (R+1) => State k),
      Fintype.sum_prod_type]
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, referenceLaw, hrel, hsnoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    calc
      _ = parryLaw k s * pathWeight k p R s v * F (relations s v) *
          ∑ t, kernel k p (endpoint R s v) t := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = _ := by rw [hrow, mul_one]
  have hnew (F : (Fin R → Bool) → ℝ) :
      (∑ v : Prefix k (R+1), referenceLaw k p (R+1) (parryLaw k) v *
        F (fun i : Fin R => prefixRelation v i.succ)) =
      ∑ v : Prefix k R, referenceLaw k p R (parryLaw k) v * F (relations v.1 v.2) := by
    have hrel (s t : State k) (v : Fin R → State k) :
        (fun i : Fin R => prefixRelation (s,Fin.cons t v) i.succ) = relations t v := by
      funext i
      simp only [prefixRelation, relations, ← Fin.succ_castSucc, Fin.cons_succ]
    have hsplit (s : State k) :
        (∑ v : Fin (R+1) → State k, referenceLaw k p (R+1) (parryLaw k) (s,v) *
          F (fun i : Fin R => prefixRelation (s,v) i.succ)) =
        ∑ t : State k, ∑ v : Fin R → State k,
          parryLaw k s * kernel k p s t * (pathWeight k p R t v * F (relations t v)) := by
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (R+1) => State k),
        Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, referenceLaw, hrel, pathWeight,
        Fin.cons_zero, Fin.cons_succ]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro v _
      ring
    rw [Fintype.sum_prod_type]
    simp_rw [hsplit]
    rw [Finset.sum_comm]
    conv_rhs => rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [← Finset.sum_mul, hstat]
    simp only [referenceLaw]
    ring
  have hlarge (h18 : 18 ≤ R) : stationaryDefect k R (sharedRule R) ≤
      4 / (((R-2)/16 : ℕ) : ℝ) +
        2 * Real.exp (-((R : ℝ)-2)/16) + (31/32 : ℝ)^(R/4) := by
    let t := R-2
    let n := t/16
    have ht : 16 ≤ t := by dsimp [t]; omega
    have hn : 1 ≤ n := by dsimp [n]; omega
    have hnt : n*16 ≤ t := Nat.div_mul_le_self t 16
    have htR : (t : ℝ) = (R : ℝ)-2 := by dsimp [t]; rw [Nat.cast_sub (by omega)]; norm_num
    let C := (D n t).filter (fun cs => size cs ≤ t)
    let S := ∑ cs ∈ C, p^(size cs)
    let M := ∑ cs ∈ C.filter maximal, p^(size cs)
    have hsize (cs : List (ℕ × ℕ)) (c : ℕ × ℕ) (hc : c ∈ cs) : c.1 ≤ size cs := by
      have h : c.1+c.2 ≤ size cs := List.le_sum_of_mem (List.mem_map.mpr ⟨c,hc,rfl⟩)
      omega
    have hfit (B : ℕ) (hB : t ≤ B) :
        (D n B).filter (fun cs => size cs ≤ t) = C := by
      ext cs
      simp only [C, Finset.mem_filter, hmemD]
      constructor
      · rintro ⟨⟨hl,hv⟩,hs⟩
        exact ⟨⟨hl,fun c hc => ⟨(hv c hc).1,(hsize cs c hc).trans hs,
          (hv c hc).2.2⟩⟩,hs⟩
      · rintro ⟨⟨hl,hv⟩,hs⟩
        exact ⟨⟨hl,fun c hc => ⟨(hv c hc).1,((hv c hc).2.1).trans hB,
          (hv c hc).2.2⟩⟩,hs⟩
    have htail (B : ℕ) (hB : t ≤ B) :
        (1-p^B)^n-S ≤ 4^n/(6/5:ℝ)^t := by
      have hsplit := Finset.sum_filter_add_sum_filter_not (D n B)
        (fun cs => size cs ≤ t) (fun cs => p^(size cs))
      rw [hfit B hB, hmassD] at hsplit
      have hpoint (cs : List (ℕ × ℕ)) (hs : t < size cs) :
          p^(size cs) ≤ (p*(6/5:ℝ))^(size cs)/(6/5:ℝ)^t := by
        apply (le_div_iff₀ (by positivity)).mpr
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hs.le)
          (pow_nonneg hp.le _)
      have hh : (∑ cs ∈ (D n B).filter (fun cs => ¬size cs ≤ t), p^(size cs)) ≤
          (∑ cs ∈ D n B, (p*(6/5:ℝ))^(size cs))/(6/5:ℝ)^t := by
        rw [Finset.sum_div]
        calc
          _ ≤ ∑ cs ∈ (D n B).filter (fun cs => ¬size cs ≤ t),
              (p*(6/5:ℝ))^(size cs)/(6/5:ℝ)^t := by
            apply Finset.sum_le_sum
            intro cs hc
            exact hpoint cs (Nat.lt_of_not_ge (Finset.mem_filter.mp hc).2)
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun cs _ _ => by positivity)
      have hm := div_le_div_of_nonneg_right (hmoment n B) (by positivity : 0 ≤ (6/5:ℝ)^t)
      dsimp only [S] at *
      linarith only [hsplit,hh,hm]
    have hS : 1-S ≤ Real.exp (-(t : ℝ)/16) := by
      have hlim : Filter.Tendsto (fun B : ℕ => (1-p^B)^n-S)
          Filter.atTop (nhds (1-S)) := by
        convert ((tendsto_const_nhds.sub
          (tendsto_pow_atTop_nhds_zero_of_lt_one hp.le hp1)).pow n).sub_const S using 1
        simp
      have hh : 1-S ≤ 4^n/(6/5:ℝ)^t :=
        le_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨t,fun B hB => htail B hB⟩)
      apply hh.trans
      have hlog4 : Real.log 4 ≤ 3/2 := by
        have h := Real.log_two_lt_d9
        have he : Real.log 4 = 2*Real.log 2 := by
          rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]; norm_num
        linarith only [h,he]
      have hlog6 : (1/6:ℝ) ≤ Real.log (6/5) := by
        have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<6/5 by norm_num)
        norm_num at h ⊢
        linarith only [h]
      have hnr : (n:ℝ)*16 ≤ t := by exact_mod_cast hnt
      have hpow (x : ℝ) (hx : 0 < x) (j : ℕ) : x^j = Real.exp ((j:ℝ)*Real.log x) := by
        rw [Real.exp_nat_mul, Real.exp_log hx]
      rw [hpow 4 (by norm_num), hpow (6/5) (by norm_num), ← Real.exp_sub]
      apply Real.exp_le_exp.mpr
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
      have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg _
      nlinarith only [hlog4,hlog6,hnr,hn0,ht0]
    have hM : M ≤ 2/(n:ℝ) := by
      have hsub : C.filter maximal ⊆ (D n t).filter maximal :=
        Finset.filter_subset_filter _ (Finset.filter_subset _ _)
      have hm : M ≤ ∑ cs ∈ (D n t).filter maximal, p^(size cs) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun cs _ _ => pow_nonneg hp.le _)
      have he : n = (n-1)+1 := by omega
      have hb : (∑ cs ∈ (D n t).filter maximal, p^(size cs)) ≤ 1/(p*(n:ℝ)) := by
        convert hmaxD (n-1) t using 1 <;>
          simp only [← he, Nat.cast_sub hn, Nat.cast_one, sub_add_cancel]
      apply hm.trans (hb.trans ?_)
      have hnp : (0:ℝ)<n := by exact_mod_cast hn
      apply (div_le_div_iff₀ (mul_pos hp hnp) hnp).mpr
      have hpHalf : 1/2 < p := hr.1
      nlinarith only [hpHalf,hnp]
    have hlen : ∀ cs ∈ C, cs.length = n := by
      intro cs hc
      exact ((hmemD n t cs).mp (Finset.mem_filter.mp hc).1).1
    have hvalid : ∀ cs ∈ C, ∀ c ∈ cs, 1 ≤ c.1 ∧ 1 ≤ c.2 ∧ c.2 < k := by
      intro cs hc c hcc
      have h := ((hmemD n t cs).mp (Finset.mem_filter.mp hc).1).2 c hcc
      exact ⟨h.1,h.2.2⟩
    have hfits : ∀ cs ∈ C, 2+(cs.map (fun c => c.1+c.2)).sum ≤ R := by
      intro cs hc
      have hs := (Finset.mem_filter.mp hc).2
      change size cs ≤ t at hs
      dsimp [t] at hs
      change 2+size cs ≤ R
      omega
    obtain ⟨hminus,hplus⟩ := parry_boundary_cylinder_bound k hk R n hn C hlen hvalid hfits
    change (∑ v : Prefix k R with ∃ c,
      selected (windowOnes (relations v.1 v.2)) R R = some c ∧ c.1=0,
      referenceLaw k p R (parryLaw k) v) ≤ stationaryWordMass k [true,false]*(1-S+M) at hminus
    change (∑ v : Prefix k R with ∃ c,
      selected (windowOnes (relations v.1 v.2)) R R = some c ∧ c.2=R-1,
      referenceLaw k p R (parryLaw k) v) ≤ stationaryWordMass k [false,true]*(1-S+M) at hplus
    let Eminus (w : Fin R → Bool) := ∃ c, selected (windowOnes w) R R = some c ∧ c.1=0
    let Eplus (w : Fin R → Bool) := ∃ c, selected (windowOnes w) R R = some c ∧ c.2=R-1
    let Ezero (w : Fin R → Bool) := selected (windowOnes w) R R = none
    have hmargMinus := hold (fun w => if Eminus w then 1 else 0)
    have hmargPlus := hnew (fun w => if Eplus w then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero] at hmargMinus hmargPlus
    have hincl : stationaryDefect k R (sharedRule R) ≤
        (∑ v : Prefix k R with Eminus (relations v.1 v.2), referenceLaw k p R (parryLaw k) v) +
        (∑ v : Prefix k R with Eplus (relations v.1 v.2), referenceLaw k p R (parryLaw k) v) +
        (∑ v : Prefix k (R+1) with Ezero (fun i : Fin R => prefixRelation v i.succ),
          referenceLaw k p (R+1) (parryLaw k) v) := by
      simp only [stationaryDefect, Finset.sum_filter]
      rw [← hmargMinus, ← hmargPlus]
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro v _
      have hv := hpos (R+1) v
      dsimp only [p] at hv ⊢
      change (if prefixRuleDefect (sharedRule R) v = true then
        referenceLaw k (parryParameter k) (R+1) (parryLaw k) v else 0) ≤ _
      by_cases hd : prefixRuleDefect (sharedRule R) v = true
      · have hi := shared_rule_defect_boundary_inclusion R (prefixRelation v) hd
        change Eminus (fun i : Fin R => prefixRelation v i.castSucc) ∨
          Eplus (fun i : Fin R => prefixRelation v i.succ) ∨
          Ezero (fun i : Fin R => prefixRelation v i.succ) at hi
        rw [if_pos hd]
        rcases hi with hi | hi | hi <;> rw [if_pos hi]
        all_goals split_ifs <;> linarith only [hv]
      · rw [if_neg hd]
        split_ifs <;> linarith only [hv]
    have hnone := (parry_no_complete_run_bound k hk R).2
    have heps : 1-S+M ≤ Real.exp (-(t:ℝ)/16)+2/(n:ℝ) := by linarith only [hS,hM]
    have hbetaMinus : stationaryWordMass k [true,false]*(1-S+M) ≤
        Real.exp (-(t:ℝ)/16)+2/(n:ℝ) := by
      calc
        _ ≤ stationaryWordMass k [true,false]*(Real.exp (-(t:ℝ)/16)+2/(n:ℝ)) :=
          mul_le_mul_of_nonneg_left heps (hmassle _).1
        _ ≤ _ := mul_le_of_le_one_left (by positivity) (hmassle _).2
    have hbetaPlus : stationaryWordMass k [false,true]*(1-S+M) ≤
        Real.exp (-(t:ℝ)/16)+2/(n:ℝ) := by
      calc
        _ ≤ stationaryWordMass k [false,true]*(Real.exp (-(t:ℝ)/16)+2/(n:ℝ)) :=
          mul_le_mul_of_nonneg_left heps (hmassle _).1
        _ ≤ _ := mul_le_of_le_one_left (by positivity) (hmassle _).2
    have hb1 := hminus.trans hbetaMinus
    have hb2 := hplus.trans hbetaPlus
    change _ ≤ (31/32:ℝ)^(R/4) at hnone
    dsimp only [Eminus,Eplus,Ezero] at hincl
    rw [htR] at hb1 hb2
    change stationaryDefect k R (sharedRule R) ≤
      4/(n:ℝ)+2*Real.exp (-((R:ℝ)-2)/16)+(31/32:ℝ)^(R/4)
    dsimp only [p] at hincl hb1 hb2
    apply hincl.trans
    convert add_le_add (add_le_add hb1 hb2) hnone using 1 <;> ring
  refine ⟨le_min hone ?_, hlarge⟩
  have hRp : (0:ℝ)<R := by exact_mod_cast hR
  by_cases h18 : 18 ≤ R
  · have hb := hlarge h18
    let t := R-2
    let n := t/16
    have ht : 16 ≤ t := by dsimp [t]; omega
    have hn : 1 ≤ n := by dsimp [n]; omega
    have hnp : (0:ℝ)<n := by exact_mod_cast hn
    have htp : (0:ℝ)<t := by exact_mod_cast (show 0<t by omega)
    have htR : (t:ℝ) = (R:ℝ)-2 := by dsimp [t]; rw [Nat.cast_sub (by omega)]; norm_num
    have htn : t ≤ 32*n := by dsimp [n]; omega
    have htnr : (t:ℝ) ≤ 32*(n:ℝ) := by exact_mod_cast htn
    have hnterm : 4/(n:ℝ) ≤ 128/(t:ℝ) := by
      apply (div_le_div_iff₀ hnp htp).mpr
      nlinarith only [htnr]
    have hexp (x : ℝ) (hx : 0<x) : Real.exp (-x) ≤ 1/x := by
      apply (le_div_iff₀ hx).mpr
      have he := Real.mul_exp_neg_le_exp_neg_one x
      have h1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      nlinarith only [he,h1]
    have heterm : 2*Real.exp (-(t:ℝ)/16) ≤ 32/(t:ℝ) := by
      have hh := hexp ((t:ℝ)/16) (by positivity)
      have he : -((t:ℝ)/16) = -(t:ℝ)/16 := by ring
      rw [he] at hh
      calc
        _ ≤ 2*(1/((t:ℝ)/16)) := mul_le_mul_of_nonneg_left hh (by norm_num)
        _ = _ := by ring
    have hbase : (31/32:ℝ) ≤ Real.exp (-(1/32:ℝ)) := by
      have hh := Real.add_one_le_exp (-(1/32:ℝ))
      linarith only [hh]
    have hfloor : R ≤ 8*(R/4) := by omega
    have hdecay : (31/32:ℝ)^(R/4) ≤ Real.exp (-(R:ℝ)/256) := by
      calc
        _ ≤ (Real.exp (-(1/32:ℝ)))^(R/4) := pow_le_pow_left₀ (by norm_num) hbase _
        _ = Real.exp ((R/4:ℕ)*(-(1/32:ℝ))) := (Real.exp_nat_mul _ _).symm
        _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have hh : (R:ℝ) ≤ 8*((R/4:ℕ):ℝ) := by exact_mod_cast hfloor
          nlinarith only [hh]
    have hpterm : (31/32:ℝ)^(R/4) ≤ 256/(R:ℝ) := by
      apply hdecay.trans
      have hh := hexp ((R:ℝ)/256) (by positivity)
      simpa only [one_div_div, neg_div] using hh
    have hrat : 160/(t:ℝ) ≤ 180/(R:ℝ) := by
      apply (div_le_div_iff₀ htp hRp).mpr
      have h18r : (18:ℝ) ≤ R := by exact_mod_cast h18
      rw [htR]
      nlinarith only [h18r]
    have hscalar : 4/(n:ℝ)+2*Real.exp (-(t:ℝ)/16)+(31/32:ℝ)^(R/4) ≤ 512/(R:ℝ) := by
      calc
        _ ≤ 128/(t:ℝ)+32/(t:ℝ)+256/(R:ℝ) := by linarith only [hnterm, heterm, hpterm]
        _ = 160/(t:ℝ)+256/(R:ℝ) := by ring
        _ ≤ 180/(R:ℝ)+256/(R:ℝ) := by linarith only [hrat]
        _ = 436/(R:ℝ) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) hRp.le
    change stationaryDefect k R (sharedRule R) ≤
      4/(n:ℝ)+2*Real.exp (-((R:ℝ)-2)/16)+(31/32:ℝ)^(R/4) at hb
    rw [htR] at hscalar
    exact hb.trans hscalar
  · apply hone.trans
    apply (le_div_iff₀ hRp).mpr
    have hr18 : (R:ℝ)<18 := by exact_mod_cast (show R<18 by omega)
    linarith only [hr18]

#print axioms parry_shared_rule_bound

end D5.S3.TotalVariation.ParrySharedRuleBound
