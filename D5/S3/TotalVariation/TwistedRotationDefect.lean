/- GID: D5/S3/TotalVariation/TwistedRotationDefect
   generality: I
   mirror-B: D5/B/S3/TotalVariation/TwistedRotationDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rotation of actual signed twisted paths gives uniform same-rule Parry defect bounds. -/

import D5.S3.TotalVariation.ParryTwistedComparison
import D5.S3.TotalVariation.TwistedSameRuleDefect

open scoped BigOperators
open D5.S3.TotalVariation.TwistedResetPaths
open D5.S3.TotalVariation.TwistedPrefixComparison
open D5.S3.TotalVariation.TwistedSameRuleDefect
open D5.S3.TotalVariation.ParryResetLaw
open D5.S3.TotalVariation.ParryTwistedComparison
namespace D5.S3.TotalVariation.TwistedRotationDefect

set_option backward.isDefEq.respectTransparency false

/-- The actual signed state path, with complement at every full turn. -/
def extension {k : ℕ} (m : ℕ) (v : Fin (m + 1) → State k) (i : ℕ) : State k :=
  (cycleSign (m+1) (by omega) (fun j => (v j).1) i,
    (v ⟨i % (m+1), Nat.mod_lt _ (by omega)⟩).2)

/-- Shift one state along the complemented path; the inverse crosses the seam backwards. -/
def rotation {k : ℕ} (m : ℕ) :
    (Fin (m + 1) → State k) ≃ (Fin (m + 1) → State k) where
  toFun v := Fin.snoc (Fin.tail v) (flip (v 0))
  invFun v := Fin.cons (flip (v (Fin.last m))) (Fin.init v)
  left_inv v := by simp [TwistedResetPaths.flip, Fin.cons_self_tail]
  right_inv v := by simp [TwistedResetPaths.flip, Fin.snoc_init_self]

/-- Full transition product, with the closing transition to the complemented start. -/
noncomputable def cycleWeight (k : ℕ) (p : ℝ) (m : ℕ)
    (v : Fin (m + 1) → State k) : ℝ :=
  ∏ i : Fin (m+1), kernel k p (extension m v i.val) (extension m v (i.val+1))

/-- Each fixed deterministic rule has twisted defect at least one over the period.
The same rule under the actual stationary Parry law satisfies the uniform window bound. -/
theorem parry_window_lower_bound (k : ℕ) (hk : 2 ≤ k)
    (R G : ℕ) (hR : 1 ≤ R) (hG : 1 ≤ G) :
    (∀ f : (Fin R → Bool) → Bool,
      1 / (R+1+G : ℕ) ≤ twistedDefect k R G f ∧
      1 / (R+1+G : ℕ) - 2 * (R+1+G : ℕ) * (3/4 : ℝ)^(G/3) -
        Real.goldenRatio^(2-((R+1+G : ℕ) : ℤ)) ≤ stationaryDefect k R f) ∧
    (∃ fmin : (Fin R → Bool) → Bool,
      (∀ f : (Fin R → Bool) → Bool, stationaryDefect k R fmin ≤ stationaryDefect k R f) ∧
      1 / (R+1+G : ℕ) - 2 * (R+1+G : ℕ) * (3/4 : ℝ)^(G/3) -
        Real.goldenRatio^(2-((R+1+G : ℕ) : ℤ)) ≤ stationaryDefect k R fmin) := by
  classical
  have hall : ∀ f : (Fin R → Bool) → Bool,
      1 / (R+1+G : ℕ) ≤ twistedDefect k R G f ∧
      1 / (R+1+G : ℕ) - 2 * (R+1+G : ℕ) * (3/4 : ℝ)^(G/3) -
        Real.goldenRatio^(2-((R+1+G : ℕ) : ℤ)) ≤ stationaryDefect k R f := by
    intro f
    obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : G ≠ 0)
    let n := R+1
    let m := n+g
    let p := parryParameter k
    let Q := kernel k p
    let Z := loopMass k p (m+1)
    let W := cycleWeight k p m
    let pre : (Fin (m + 1) → State k) → Prefix k n := fun v =>
      (v 0, fun i => v ⟨i.val+1,by dsimp [m]; omega⟩)
    have hbase (v : Fin (m + 1) → State k) (i : ℕ) (hi : i < m+1) :
        extension m v i = v ⟨i,hi⟩ := by
      simp [extension, cycleSign, Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi]
    have hlast (v : Fin (m + 1) → State k) :
        extension m v (m+1) = flip (v 0) := by
      simp [extension,cycleSign,TwistedResetPaths.flip]
    have hpath : ∀ (a : ℕ) (v : Fin (a+1) → State k),
        pathWeight k p a (v 0) (Fin.tail v) =
          ∏ i : Fin a, Q (v i.castSucc) (v i.succ) ∧
        endpoint a (v 0) (Fin.tail v) = v (Fin.last a) := by
      intro a
      induction a with
      | zero => intro v; simp [pathWeight,endpoint]
      | succ a ih =>
        intro v
        obtain ⟨hw,he⟩ := ih (Fin.tail v)
        constructor
        · simpa +unfoldPartialApp only [pathWeight, Fin.tail, Fin.prod_univ_succ,
            Fin.succ_zero_eq_one,
            Fin.castSucc_zero, Fin.castSucc_succ, Q] using congrArg
              (fun x => kernel k p (v 0) (v 1) * x) hw
        · simpa +unfoldPartialApp only [endpoint, Fin.tail, Fin.succ_zero_eq_one,
            Fin.succ_last] using he
    have hsnoc (a : ℕ) (s t : State k) (v : Fin a → State k) :
        endpoint (a+1) s (Fin.snoc v t) = t ∧
        pathWeight k p (a+1) s (Fin.snoc v t) =
          pathWeight k p a s v * Q (endpoint a s v) t := by
      have h₁ := hpath (a+1) (Fin.cons s (Fin.snoc v t))
      have h₂ := hpath a (Fin.cons s v)
      constructor
      · simpa using h₁.2
      · simp only [Fin.tail_cons, Fin.cons_zero] at h₁ h₂
        rw [h₁.1, Fin.prod_univ_castSucc, h₂.1, h₂.2]
        simp only [Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc, Fin.snoc_last,
          ← Fin.castSucc_succ, Fin.succ_last]
    have happend : ∀ (a b : ℕ) (s : State k) (v : Fin a → State k) (w : Fin b → State k),
        endpoint (a+b) s (Fin.append v w) = endpoint b (endpoint a s v) w ∧
        pathWeight k p (a+b) s (Fin.append v w) =
          pathWeight k p a s v * pathWeight k p b (endpoint a s v) w := by
      intro a b
      induction b with
      | zero =>
        intro s v w
        simp [Fin.append_right_nil v w rfl,endpoint,pathWeight]
      | succ b ih =>
        intro s v w
        rw [← Fin.snoc_init_self w, Fin.append_snoc]
        obtain ⟨he,hw⟩ := ih s v (Fin.init w)
        constructor
        · calc
            _ = w (Fin.last b) := by
              convert (hsnoc (a+b) s (w (Fin.last b)) (Fin.append v (Fin.init w))).1 using 1
              congr 1
            _ = _ := (hsnoc b (endpoint a s v) (w (Fin.last b)) (Fin.init w)).1.symm
        · calc
            _ = pathWeight k p (a+b) s (Fin.append v (Fin.init w)) *
                Q (endpoint (a+b) s (Fin.append v (Fin.init w))) (w (Fin.last b)) := by
              convert (hsnoc (a+b) s (w (Fin.last b)) (Fin.append v (Fin.init w))).2 using 1
              congr 1
            _ = _ := by
              rw [(hsnoc b (endpoint a s v) (w (Fin.last b)) (Fin.init w)).2,he,hw,mul_assoc]
    have hcycle (v : Fin (m + 1) → State k) :
        W v = pathWeight k p m (v 0) (Fin.tail v) *
          Q (endpoint m (v 0) (Fin.tail v)) (flip (v 0)) := by
      dsimp [W,cycleWeight]
      rw [Fin.prod_univ_castSucc, (hpath m v).1, (hpath m v).2]
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        simp only [Fin.val_castSucc]
        rw [hbase v i.val (by omega), hbase v (i.val+1) (by omega)]
        rfl
      · simp only [Fin.val_last]
        rw [hbase v m (by omega), hlast]
        rfl
    have hpre (s : State k) (v : Fin n → State k) (w : Fin g → State k) :
        pre (Fin.cons s (Fin.append v w)) = (s,v) := by
      apply Prod.ext
      · simp [pre]
      · funext i
        change (Fin.cons s (Fin.append v w) : Fin (m + 1) → State k)
          (Fin.castAdd g i).succ = v i
        simp
    have hcompletion (s : State k) (v : Fin n → State k) :
        twistedPrefixMass k p n (g+1) s v =
          ∑ w : Fin g → State k, W (Fin.cons s (Fin.append v w)) := by
      unfold twistedPrefixMass
      rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (g+1) => State k))]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk]
      simp_rw [hsnoc]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      apply Finset.sum_congr rfl
      intro w _
      rw [hcycle]
      simp only [Fin.cons_zero,Fin.tail_cons]
      rw [(happend n g s v w).1,(happend n g s v w).2]
      ring
    have hmarg (F : Prefix k n → ℝ) :
        (∑ v : Fin (m + 1) → State k, W v * F (pre v)) =
          ∑ x : Prefix k n, twistedPrefixMass k p n (g+1) x.1 x.2 * F x := by
      conv_lhs => rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m+1) => State k)),
        Fintype.sum_prod_type]
      conv_rhs => rw [Fintype.sum_prod_type]
      simp only [Fin.consEquiv,Equiv.coe_fn_mk]
      apply Finset.sum_congr rfl
      intro s _
      rw [← Equiv.sum_comp (Fin.appendEquiv n g),Fintype.sum_prod_type]
      simp only [Fin.appendEquiv,Equiv.coe_fn_mk,hpre,hcompletion,Finset.sum_mul]
    have htotal : ∑ v, W v = Z := by
      have h := hmarg (fun _ => 1)
      simp only [mul_one] at h
      rw [h,Fintype.sum_prod_type,twisted_prefix_total_mass]
      rfl
    have hrotation :
        (∀ (v : Fin (m + 1) → State k) (i : ℕ),
          extension m (rotation m v) i = extension m v (i+1)) ∧
        (∀ v : Fin (m + 1) → State k, cycleWeight k p m (rotation m v) = cycleWeight k p m v) := by
      have hbase (v : Fin (m + 1) → State k) (i : ℕ) (hi : i < m+1) :
          extension m v i = v ⟨i,hi⟩ := by
        simp [extension, cycleSign, Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi]
      have hperiod (v : Fin (m + 1) → State k) (i : ℕ) :
          extension m v (i+(m+1)) = flip (extension m v i) := by
        have hd : (i+(m+1))/(m+1) = i/(m+1)+1 := by
          rw [Nat.add_div (by omega : 0 < m+1)]
          simp [Nat.div_self (by omega : 0 < m+1), Nat.not_le.mpr (Nat.mod_lt i (by omega : 0 < m+1))]
        have hp : decide (((i/(m+1)+1)%2)=1) = !(decide ((i/(m+1))%2=1)) := by
          by_cases h : (i/(m+1))%2=1
          · have hh : (i/(m+1)+1)%2 ≠ 1 := by omega
            simp [h,hh]
          · have hh : (i/(m+1)+1)%2 = 1 := by omega
            simp [h,hh]
        simp only [extension, cycleSign, Nat.add_mod_right, hd, hp, TwistedResetPaths.flip]
        congr 1
        cases (v ⟨i%(m+1),Nat.mod_lt _ (by omega)⟩).1 <;>
          cases decide ((i/(m+1))%2=1) <;> rfl
      have hr (v : Fin (m + 1) → State k) (i : Fin (m+1)) :
          rotation m v i = extension m v (i.val+1) := by
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [rotation, Equiv.coe_fn_mk, Fin.snoc_last, Fin.val_last]
          simpa [hbase] using (hperiod v 0).symm
        · simp only [rotation, Equiv.coe_fn_mk, Fin.snoc_castSucc, Fin.val_castSucc]
          rw [hbase v (j.val+1) (by omega)]
          rfl
      have hshift (v : Fin (m + 1) → State k) (i : ℕ) :
          extension m (rotation m v) i = extension m v (i+1) := by
        induction i using Nat.strong_induction_on with
        | h i ih =>
          by_cases hi : i < m+1
          · rw [hbase _ i hi]
            exact hr v ⟨i,hi⟩
          · have he : i = (i-(m+1))+(m+1) := by omega
            rw [he, hperiod, show i-(m+1)+(m+1)+1 = (i-(m+1)+1)+(m+1) by omega,
              hperiod, ih (i-(m+1)) (by omega)]
      refine ⟨hshift, ?_⟩
      have hQ (s t : State k) : kernel k p (flip s) (flip t) = kernel k p s t := by
        rcases s with ⟨a,j⟩
        rcases t with ⟨b,l⟩
        cases a <;> cases b <;> simp [kernel,TwistedResetPaths.flip]
      intro v
      unfold cycleWeight
      simp_rw [hshift]
      rw [Fin.prod_univ_castSucc, Fin.prod_univ_succ]
      have hend : kernel k p (extension m v (m+1)) (extension m v (m+1+1)) =
          kernel k p (extension m v 0) (extension m v 1) := by
        rw [show m+1 = 0+(m+1) by omega,
          show 0+(m+1)+1 = 1+(m+1) by omega, hperiod, hperiod, hQ]
      simpa only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero, zero_add,
        hend] using mul_comm
          (∏ i : Fin m, kernel k p (extension m v (i.val+1)) (extension m v (i.val+1+1)))
          (kernel k p (extension m v 0) (extension m v 1))

    obtain ⟨hshift,hweight⟩ := hrotation
    change ∀ v, W (rotation m v) = W v at hweight
    let D : (Fin (m + 1) → State k) → ℕ → Bool := fun v t =>
      ruleDefect (m+1) (by omega) (fun i => (v i).1) R f t
    have hrelrot (v : Fin (m + 1) → State k) (i : ℕ) :
        cycleRelation (m+1) (by omega) (fun j => (rotation m v j).1) i =
          cycleRelation (m+1) (by omega) (fun j => (v j).1) (i+1) := by
      change (!(xor (extension m (rotation m v) i).1
        (extension m (rotation m v) (i+1)).1)) =
          (!(xor (extension m v (i+1)).1 (extension m v (i+1+1)).1))
      rw [hshift,hshift]
    have hDrot (v : Fin (m + 1) → State k) (t : ℕ) : D (rotation m v) t = D v (t+1) := by
      dsimp [D,ruleDefect,ruleValue]
      simp_rw [hrelrot]
      simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    have hvec (v : Fin (m + 1) → State k) (i : Fin (n+1)) :
        (Fin.cons (pre v).1 (pre v).2 : Fin (n+1) → State k) i =
          extension m v i.val := by
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [pre,hbase]
      · simp only [Fin.cons_succ,Fin.val_succ]
        rw [hbase v (j.val+1) (by dsimp [m]; omega)]
    have hrelpre (v : Fin (m + 1) → State k) (i : Fin (R+1)) :
        prefixRelation (pre v) i =
          cycleRelation (m+1) (by omega) (fun j => (v j).1) i.val := by
      dsimp only [prefixRelation]
      rw [hvec v i.castSucc,hvec v i.succ]
      rfl
    have hDpre (v : Fin (m + 1) → State k) : D v 0 = prefixRuleDefect f (pre v) := by
      dsimp [prefixRuleDefect,D,ruleDefect,ruleValue]
      simp_rw [hrelpre]
      simp only [Fin.val_succ,Fin.val_castSucc,Fin.val_last,zero_add,Nat.add_comm 1]
    let A : ℕ → ℝ := fun t => ∑ v : Fin (m + 1) → State k,
      W v * if D v t then 1 else 0
    have hstep (t : ℕ) : A (t+1) = A t := by
      calc
        A (t+1) = ∑ v : Fin (m + 1) → State k,
            W (rotation m v) * if D (rotation m v) t then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro v _
          rw [hDrot,hweight]
        _ = A t := by
          simpa only [A] using Equiv.sum_comp (rotation m)
            (fun v => W v * if D v t then (1:ℝ) else 0)
    have hA (t : ℕ) : A t = A 0 := by
      induction t with
      | zero => rfl
      | succ t ih => exact (hstep t).trans ih
    obtain ⟨hr,_,_,hQ,_,_,_,_,_⟩ := parry_stationary_law k hk
    have hp : 0 < p := by dsimp [p]; linarith [hr.1]
    have hW (v : Fin (m + 1) → State k) : 0 ≤ W v :=
      Finset.prod_nonneg fun i _ => hQ _ _
    have hZ : 0 < Z := loop_mass_pos k hk p hp (m+1) (by dsimp [m,n]; omega)
    have hcount (v : Fin (m + 1) → State k) :
        (1:ℝ) ≤ ∑ t ∈ Finset.range (m+1), if D v t then (1:ℝ) else 0 := by
      have h := (twisted_same_rule_forces_defect (m+1) (by omega)
        (fun i => (v i).1) R f).2
      exact_mod_cast h
    have haverage : Z ≤ (m+1 : ℕ) * A 0 := by
      calc
        Z = ∑ v, W v := htotal.symm
        _ ≤ ∑ v, W v * ∑ t ∈ Finset.range (m+1), if D v t then (1:ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro v _
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (hcount v) (hW v)
        _ = ∑ t ∈ Finset.range (m+1), A t := by
          simp only [Finset.mul_sum,A]
          rw [Finset.sum_comm]
        _ = (m+1 : ℕ) * A 0 := by simp [hA]
    have hevent : A 0 / Z = twistedDefect k R (g+1) f := by
      have hm := hmarg (fun x => if prefixRuleDefect f x then (1:ℝ) else 0)
      have he : A 0 = ∑ x : Prefix k n,
          twistedPrefixMass k p n (g+1) x.1 x.2 *
            if prefixRuleDefect f x then (1:ℝ) else 0 := by
        simpa only [A,hDpre] using hm
      rw [he,Finset.sum_div]
      unfold twistedDefect twistedLaw
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp [Z,m,n,p,Nat.add_assoc]
    have hlower : 1 / (R+1+(g+1) : ℕ) ≤ twistedDefect k R (g+1) f := by
      rw [← hevent]
      have hL : (0:ℝ) < (m+1 : ℕ) := by positivity
      have h : 1 / (m+1 : ℕ) ≤ A 0 / Z := by
        apply (le_div_iff₀ hZ).mpr
        rw [one_div,inv_mul_eq_div]
        exact (div_le_iff₀ hL).mpr (by nlinarith [haverage])
      simpa only [m,n,Nat.add_assoc] using h
    refine ⟨hlower,?_⟩
    have hc := (parry_mixing_and_complete_prefix k hk).2.2 R (g+1) hR (by omega) f
    have hb := (abs_le.mp hc).2
    linarith
  obtain ⟨fmin,hmin⟩ := Finite.exists_min (stationaryDefect k R)
  exact ⟨hall,fmin,hmin,(hall fmin).2⟩

#print axioms parry_window_lower_bound
end D5.S3.TotalVariation.TwistedRotationDefect
