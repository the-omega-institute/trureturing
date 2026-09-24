/- GID: D5/S3/TotalVariation/ParrySharedZeroRule
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParrySharedZeroRule
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Parry run cylinders and uniform absence of complete zero runs. -/

import D5.S3.ObserverMemory.Trajectories.LongestZeroSelectorResponse
import D5.S3.TotalVariation.ParryWordCollision
import D5.S3.TotalVariation.ParryTwistedComparison

open scoped BigOperators
open D5.S3.ObserverMemory.Trajectories.LongestZeroSelectorResponse
open D5.S3.ObserverMemory.Trajectories.ZeroRunWordGeometry
open D5.S3.TotalVariation.TwistedResetPaths
open D5.S3.TotalVariation.TwistedPrefixComparison
open D5.S3.TotalVariation.ParryResetLaw
open D5.S3.TotalVariation.ParryWordCollision
open D5.S3.TotalVariation.ParryTwistedComparison

namespace D5.S3.TotalVariation.ParrySharedZeroRule

set_option autoImplicit false

/-- The observed one positions in a finite relation window. -/
noncomputable def windowOnes {R : ℕ} (w : Fin R → Bool) : Finset ℕ :=
  (Finset.univ.filter (fun i : Fin R => w i = true)).image Fin.val

/-- Length first, latest closing endpoint on ties, with transport strictly after
that closing one. The same table applies to every source parameter. -/
noncomputable def sharedRule (R : ℕ) (w : Fin R → Bool) : Bool :=
  decide (direction (windowOnes w) R R = 1)

/-- Continue from the already observed first zero of a run. Each pair records
its complete zero-run length and the following complete one-run length. The
final zero of a block is the first zero of the next block. -/
def runContinuation (cs : List (ℕ × ℕ)) : List Bool :=
  cs.flatMap fun c => List.replicate (c.1-1) false ++ List.replicate c.2 true ++ [false]

/-- Conditional word mass from a signed state, summed over actual state paths. -/
noncomputable def wordMass (k : ℕ) (s : State k) (w : List Bool) : ℝ :=
  ∑ v : Fin w.length → State k with List.ofFn (relations s v) = w,
    pathWeight k (parryParameter k) w.length s v

/-- Actual stationary Parry cylinder mass, using the frozen finite prefix law. -/
noncomputable def stationaryWordMass (k : ℕ) (w : List Bool) : ℝ :=
  ∑ v : Prefix k w.length with List.ofFn (relations v.1 v.2) = w,
    referenceLaw k (parryParameter k) w.length (parryLaw k) v

set_option maxHeartbeats 1200000 in
-- State-path summation and arbitrary finite concatenations are proved together.
/-- At an actual `10` boundary forward, or an actual `01` boundary backward,
every finite list of complete zero/one run lengths has the product of the
source run masses. No window-containment event is conditioned on. -/
theorem parry_complete_run_laws (k : ℕ) (hk : 2 ≤ k)
    (cs : List (ℕ × ℕ))
    (hcs : ∀ c ∈ cs, 1 ≤ c.1 ∧ 1 ≤ c.2 ∧ c.2 < k) :
    (stationaryWordMass k ([true, false] ++ runContinuation cs) /
        stationaryWordMass k [true, false] =
      (cs.map (fun c => ((1 - parryParameter k) * parryParameter k^(c.1-1)) *
        (parryParameter k^(c.2+1) / (1 - parryParameter k)))).prod) ∧
    (stationaryWordMass k ([true, false] ++ runContinuation cs).reverse /
        stationaryWordMass k [false, true] =
      (cs.map (fun c => ((1 - parryParameter k) * parryParameter k^(c.1-1)) *
        (parryParameter k^(c.2+1) / (1 - parryParameter k)))).prod) := by
  classical
  let p := parryParameter k
  let mass := wordMass k
  let z : Fin k := ⟨0, by omega⟩
  obtain ⟨hr, hb, hS, hQ, hrow, hπ, hπsum, _, _⟩ := parry_stationary_law k hk
  have hp : 0 < p := by dsimp [p]; linarith [hr.1]
  have hp1 : p < 1 := lt_of_le_of_lt hr.2.1
    (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
  have hq : 1-p ≠ 0 := by linarith
  have hh (j : Fin k) : 0 < suffixWeight k p j := lt_of_lt_of_le hp (hb j).1
  have hz : suffixWeight k p z = 1 := by
    simpa [suffixWeight, rootSum, z] using hr.2.2
  have hstep (s : State k) (b : Bool) (w : List Bool) :
      mass s (b :: w) = ∑ t : State k,
        if (!(xor s.1 t.1)) = b then kernel k p s t * mass t w else 0 := by
    dsimp [mass, wordMass]
    rw [Finset.sum_filter,
      ← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (w.length+1) => State k),
      Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, pathWeight, Fin.cons_zero, Fin.cons_succ]
    have he (t : State k) (v : Fin w.length → State k) :
        List.ofFn (relations s (Fin.cons t v)) = b :: w ↔
          (!(xor s.1 t.1)) = b ∧ List.ofFn (relations t v) = w := by
      rw [List.ofFn_succ]
      have ht : (fun i : Fin w.length => relations s (Fin.cons t v) i.succ) =
          relations t v := by
        funext i
        simp only [relations, ← Fin.succ_castSucc, Fin.cons_succ]
      rw [ht]
      simp only [relations, Fin.castSucc_zero, Fin.cons_zero, List.cons.injEq]
    apply Finset.sum_congr rfl
    intro t _
    simp only [he, Finset.sum_filter]
    by_cases hbit : (!(xor s.1 t.1)) = b
    · simp only [hbit, true_and, if_true, Finset.mul_sum, mul_ite, mul_zero]
      rfl
    · simp [hbit]
  have hnil (s : State k) : mass s [] = 1 := by
    simp [mass, wordMass, pathWeight]
  have hcons (c : ℕ × ℕ) (ds : List (ℕ × ℕ)) :
      runContinuation (c :: ds) = List.replicate (c.1-1) false ++
        (List.replicate c.2 true ++ false :: runContinuation ds) := by
    simp [runContinuation, List.append_assoc]
  have hfalse (s : State k) (w : List Bool) :
      mass s (false :: w) = p / suffixWeight k p s.2 * mass (!s.1,z) w := by
    rw [hstep]
    have he (t : State k) :
        (if (!(xor s.1 t.1)) = false then kernel k p s t * mass t w else 0) =
          if t = (!s.1,z) then p / suffixWeight k p s.2 * mass (!s.1,z) w else 0 := by
      rcases s with ⟨a,j⟩
      rcases t with ⟨b,l⟩
      cases a <;> cases b <;> simp [kernel, z, Prod.ext_iff, Fin.ext_iff]
      all_goals split_ifs with h
      all_goals try rfl
      all_goals have he : l = z := Fin.ext h
      all_goals simp [he, z]
    simp_rw [he]
    simp
  have htrue (a : Bool) (j : ℕ) (hj : j+1 < k) (w : List Bool) :
      mass (a, ⟨j,by omega⟩) (true :: w) =
        p * suffixWeight k p ⟨j+1,hj⟩ / suffixWeight k p ⟨j,by omega⟩ *
          mass (a, ⟨j+1,hj⟩) w := by
    rw [hstep]
    have he (t : State k) :
        (if (!(xor a t.1)) = true then kernel k p (a,⟨j,by omega⟩) t * mass t w else 0) =
          if t = (a,⟨j+1,hj⟩) then
            p * suffixWeight k p ⟨j+1,hj⟩ / suffixWeight k p ⟨j,by omega⟩ *
              mass (a,⟨j+1,hj⟩) w else 0 := by
      rcases t with ⟨b,l⟩
      cases a <;> cases b <;> simp [kernel, Prod.ext_iff, Fin.ext_iff]
      all_goals split_ifs with h
      all_goals try rfl
      all_goals have he : l = ⟨j+1,hj⟩ := Fin.ext h
      all_goals simp [he]
    simp_rw [he]
    simp
  have hone (a : Bool) (j n : ℕ) (hjn : j+n < k) (w : List Bool) :
      mass (a,⟨j,by omega⟩) (List.replicate n true ++ w) =
        p^n * suffixWeight k p ⟨j+n,hjn⟩ / suffixWeight k p ⟨j,by omega⟩ *
          mass (a,⟨j+n,hjn⟩) w := by
    induction n generalizing j with
    | zero => simp [(hh _).ne']
    | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [htrue a j (by omega), ih (j+1) (by omega), pow_succ]
      have he : (⟨j+1+n,by omega⟩ : Fin k) = ⟨j+(n+1),hjn⟩ := by
        apply Fin.ext
        dsimp
        omega
      rw [he]
      field_simp [(hh ⟨j,by omega⟩).ne', (hh ⟨j+1,by omega⟩).ne']
  have hzero (w : List Bool) (C : ℝ) (hC : ∀ a : Bool, mass (a,z) w = C)
      (n : ℕ) (a : Bool) : mass (a,z) (List.replicate n false ++ w) = p^n*C := by
    induction n generalizing a with
    | zero => simpa using hC a
    | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [hfalse, ih, hz, div_one, pow_succ]
      ring
  let factor (c : ℕ × ℕ) := ((1-p)*p^(c.1-1))*(p^(c.2+1)/(1-p))
  have hrun (ds : List (ℕ × ℕ)) (hds : ∀ c ∈ ds, 1 ≤ c.1 ∧ 1 ≤ c.2 ∧ c.2 < k)
      (a : Bool) : mass (a,z) (runContinuation ds) = (ds.map factor).prod := by
    induction ds generalizing a with
    | nil => simp [runContinuation, hnil]
    | cons c ds ih =>
      obtain ⟨hc0,hc1,hck⟩ := hds c (by simp)
      have ht : ∀ d ∈ ds, 1 ≤ d.1 ∧ 1 ≤ d.2 ∧ d.2 < k :=
        fun d hd => hds d (by simp [hd])
      have hC (a : Bool) :
          mass (a,z) (List.replicate c.2 true ++ false :: runContinuation ds) =
            p^(c.2+1) * (ds.map factor).prod := by
        have hh1 := hone a 0 c.2 (by simpa using hck) (false :: runContinuation ds)
        change mass (a,z) (List.replicate c.2 true ++ false :: runContinuation ds) = _ at hh1
        rw [hh1, hfalse, ih ht, hz]
        simp only [zero_add]
        field_simp [(hh ⟨c.2,hck⟩).ne']
        rw [pow_succ]
        ring
      rw [hcons]
      rw [hzero _ _ hC]
      simp only [List.map_cons, List.prod_cons, factor]
      field_simp [hq]
  have hstationary (w : List Bool) :
      stationaryWordMass k w = ∑ s : State k, parryLaw k s * mass s w := by
    simp only [stationaryWordMass, wordMass, mass, Finset.sum_filter,
      Fintype.sum_prod_type, referenceLaw, Finset.mul_sum, mul_ite, mul_zero]
  have hboundary (s : State k) :
      mass s ([true,false] ++ runContinuation cs) =
        mass s [true,false] * (cs.map factor).prod := by
    simp only [List.cons_append, List.nil_append]
    rw [hstep, hstep]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [hfalse, hfalse, hrun cs hcs, hnil]
    split_ifs <;> ring
  have hboundary_pos : 0 < stationaryWordMass k [true,false] := by
    rw [hstationary]
    have hmass_nonneg (s : State k) (w : List Bool) : 0 ≤ mass s w := by
      have hw : ∀ (n : ℕ) (s : State k) (v : Fin n → State k),
          0 ≤ pathWeight k p n s v := by
        intro n
        induction n with
        | zero => intro s v; exact zero_le_one
        | succ n ih => intro s v; exact mul_nonneg (hQ _ _) (ih _ _)
      exact Finset.sum_nonneg fun v _ => hw _ _ _
    have hpi0 : 0 < parryLaw k (false,z) := by
      have hS0 : 0 < normalizer k := by linarith
      simp only [parryLaw]
      change 0 < p^z.val * suffixWeight k p z / (2*normalizer k)
      rw [hz]
      positivity
    have hm0 : mass (false,z) [true,false] = p^2 := by
      have ht := htrue false 0 (by omega) [false]
      change mass (false,z) [true,false] = _ at ht
      rw [ht, hfalse, hnil, hz]
      field_simp [(hh ⟨1,by omega⟩).ne']
    apply lt_of_lt_of_le (b := parryLaw k (false,z) * mass (false,z) [true,false])
    · rw [hm0]
      exact mul_pos hpi0 (pow_pos hp _)
    · exact Finset.single_le_sum (fun s _ => mul_nonneg (hπ s) (hmass_nonneg s _))
        (Finset.mem_univ (false,z))
  have hjoint : stationaryWordMass k ([true,false] ++ runContinuation cs) =
      stationaryWordMass k [true,false] * (cs.map factor).prod := by
    rw [hstationary, hstationary]
    simp_rw [hboundary, ← mul_assoc, ← Finset.sum_mul]
  constructor
  · change stationaryWordMass k ([true,false] ++ runContinuation cs) /
      stationaryWordMass k [true,false] = (cs.map factor).prod
    rw [hjoint]
    exact mul_div_cancel_left₀ _ hboundary_pos.ne'
  · let piece (c : ℕ × ℕ) := List.replicate c.2 true ++ List.replicate c.1 false
    let tail (ds : List (ℕ × ℕ)) := ds.flatMap piece ++ [true]
    let C := p * suffixWeight k p ⟨1,by omega⟩
    have hsingle (a : Bool) : mass (a,z) [true] = C := by
      have ht := htrue a 0 (by omega) []
      change mass (a,z) [true] = _ at ht
      rw [ht, hnil, hz]
      simp [C]
    have htail (ds : List (ℕ × ℕ))
        (hds : ∀ c ∈ ds, 1 ≤ c.1 ∧ 1 ≤ c.2 ∧ c.2 < k) (a : Bool) :
        mass (a,z) (tail ds) = C * (ds.map factor).prod := by
      induction ds generalizing a with
      | nil => simpa [tail] using hsingle a
      | cons c ds ih =>
        obtain ⟨hc0,hc1,hck⟩ := hds c (by simp)
        have ht : ∀ d ∈ ds, 1 ≤ d.1 ∧ 1 ≤ d.2 ∧ d.2 < k :=
          fun d hd => hds d (by simp [hd])
        have hrem (a : Bool) : mass (a,z) (tail ds) = C * (ds.map factor).prod := ih ht a
        have hword : tail (c :: ds) = List.replicate c.2 true ++
            false :: (List.replicate (c.1-1) false ++ tail ds) := by
          have he : c.1 = (c.1-1)+1 := by omega
          dsimp [tail, piece]
          rw [List.flatMap_cons, List.append_assoc, he, List.replicate_succ]
          simp [List.append_assoc]
        rw [hword, hone a 0 c.2 (by simpa using hck), hfalse]
        rw [hzero _ _ hrem, hz]
        simp only [zero_add, List.map_cons, List.prod_cons, factor]
        field_simp [hq, (hh ⟨c.2,hck⟩).ne']
        rw [pow_succ]
        ring
    have hword (ds : List (ℕ × ℕ))
        (hds : ∀ c ∈ ds, 1 ≤ c.1 ∧ 1 ≤ c.2 ∧ c.2 < k) :
        (runContinuation ds).reverse ++ [false] = false :: ds.reverse.flatMap piece := by
      induction ds with
      | nil => rfl
      | cons c ds ih =>
        obtain ⟨hc0,hc1,hck⟩ := hds c (by simp)
        have ht : ∀ d ∈ ds, 1 ≤ d.1 ∧ 1 ≤ d.2 ∧ d.2 < k :=
          fun d hd => hds d (by simp [hd])
        have hzword : List.replicate (c.1-1) false ++ [false] =
            List.replicate c.1 false := by
          change List.replicate (c.1-1) false ++ List.replicate 1 false = _
          rw [← List.replicate_add]
          congr 1
          omega
        rw [hcons]
        simp only [List.reverse_append, List.reverse_cons,
          List.reverse_replicate, List.reverse_cons, List.flatMap_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [ih ht]
        simp only [List.cons_append, List.append_assoc, hzword, piece]
    have hfull : ([true,false] ++ runContinuation cs).reverse = false :: tail cs.reverse := by
      have hw := hword cs hcs
      simpa [List.reverse_append, List.append_assoc, tail] using
        congrArg (fun w => w ++ [true]) hw
    have hback (s : State k) :
        mass s ([true,false] ++ runContinuation cs).reverse =
          mass s [false,true] * (cs.map factor).prod := by
      rw [hfull, hfalse, hfalse, hsingle, htail cs.reverse]
      · rw [List.map_reverse, List.prod_reverse]
        ring
      · intro c hc
        exact hcs c (List.mem_reverse.mp hc)
    have hback_pos : 0 < stationaryWordMass k [false,true] := by
      rw [hstationary]
      have hCpos : 0 < C := mul_pos hp (hh _)
      have hmpos (s : State k) : 0 < mass s [false,true] := by
        rw [hfalse, hsingle]
        exact mul_pos (div_pos hp (hh _)) hCpos
      have hpi0 : 0 < parryLaw k (false,z) := by
        have hS0 : 0 < normalizer k := by linarith
        change 0 < p^z.val * suffixWeight k p z / (2*normalizer k)
        rw [hz]
        positivity
      apply lt_of_lt_of_le (mul_pos hpi0 (hmpos (false,z)))
      exact Finset.single_le_sum (fun s _ => mul_nonneg (hπ s) (hmpos s).le)
        (Finset.mem_univ (false,z))
    have hjoint_back : stationaryWordMass k ([true,false] ++ runContinuation cs).reverse =
        stationaryWordMass k [false,true] * (cs.map factor).prod := by
      rw [hstationary, hstationary]
      simp_rw [hback, ← mul_assoc, ← Finset.sum_mul]
    change stationaryWordMass k ([true,false] ++ runContinuation cs).reverse /
      stationaryWordMass k [false,true] = (cs.map factor).prod
    rw [hjoint_back]
    exact mul_div_cancel_left₀ _ hback_pos.ne'

set_option maxHeartbeats 1200000 in
-- Finite path sums and the four-transition conditioning are elaborated together.
/-- The empty branch of the original complete-run selector has uniformly
exponentially small mass, both conditionally on a signed starting state and
in the new window of the actual stationary defect prefix. -/
theorem parry_no_complete_run_bound (k : ℕ) (hk : 2 ≤ k) (R : ℕ) :
    (∀ s : State k,
      (∑ v : Fin R → State k with
        candidates (windowOnes (relations s v)) R R = ∅,
        pathWeight k (parryParameter k) R s v) ≤ (31/32 : ℝ)^(R/4)) ∧
    ((∑ v : Prefix k (R+1) with
        selected (windowOnes (fun i : Fin R => prefixRelation v i.succ)) R R = none,
        referenceLaw k (parryParameter k) (R+1) (parryLaw k) v) ≤
      (31/32 : ℝ)^(R/4)) := by
  classical
  let p := parryParameter k
  let E (n : ℕ) (s : State k) (v : Fin n → State k) :=
    candidates (windowOnes (relations s v)) n n = ∅
  obtain ⟨hr, hb, _, hQ, hrow, hπ, hπsum, _, _⟩ := parry_stationary_law k hk
  have hp : 0 < p := by dsimp [p]; linarith [hr.1]
  have hh (j : Fin k) : 0 < suffixWeight k p j := lt_of_lt_of_le hp (hb j).1
  let z : Fin k := ⟨0, by omega⟩
  let o : Fin k := ⟨1, by omega⟩
  have hz : suffixWeight k p z = 1 := by
    simpa [suffixWeight, rootSum, z] using hr.2.2
  have hw : ∀ (n : ℕ) (s : State k) (v : Fin n → State k),
      0 ≤ pathWeight k p n s v := by
    intro n
    induction n with
    | zero => intro s v; exact zero_le_one
    | succ n ih => intro s v; exact mul_nonneg (hQ _ _) (ih _ _)
  have hrows : ∀ (n : ℕ) (s : State k),
      (∑ v : Fin n → State k, pathWeight k p n s v) = 1 := by
    intro n
    induction n with
    | zero => intro s; simp [pathWeight]
    | succ n ih =>
      intro s
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n+1) => State k)]
      rw [Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, pathWeight,
        Fin.cons_zero, Fin.cons_succ]
      simp_rw [← Finset.mul_sum, ih, mul_one]
      exact hrow s
  have hend : ∀ (l : ℕ) (s : State k) (v : Fin l → State k),
      endpoint l s v = (Fin.cons s v : Fin (l+1) → State k) (Fin.last l) := by
    intro l
    induction l with
    | zero => intro s v; rfl
    | succ l ih =>
      intro s v
      have hv : (Fin.cons (v 0) (fun i : Fin l => v i.succ) :
          Fin (l+1) → State k) = v := Fin.cons_self_tail v
      rw [endpoint, ih, hv, Fin.cons_last]
  have hprod : ∀ (l : ℕ) (s : State k) (v : Fin l → State k),
      pathWeight k p l s v =
        ∏ i : Fin l, kernel k p ((Fin.cons s v : Fin (l+1) → State k) i.castSucc) (v i) := by
    intro l
    induction l with
    | zero => intro s v; simp [pathWeight]
    | succ l ih =>
      intro s v
      have hv : (Fin.cons (v 0) (fun i : Fin l => v i.succ) :
          Fin (l+1) → State k) = v := Fin.cons_self_tail v
      rw [pathWeight, ih, hv, Fin.prod_univ_succ]
      simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]
  have hpre (l r : ℕ) (s : State k) (u : Fin l → State k) (v : Fin r → State k)
      (i : Fin l) :
      (Fin.cons s (Fin.append u v) : Fin (l+r+1) → State k) (i.castAdd r).castSucc =
        (Fin.cons s u : Fin (l+1) → State k) i.castSucc := by
    cases l with
    | zero => exact Fin.elim0 i
    | succ l =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · have he : (j.succ.castAdd r).castSucc = (j.castSucc.castAdd r).succ := by
          apply Fin.ext; rfl
        rw [he, Fin.cons_succ, Fin.append_left, ← Fin.succ_castSucc, Fin.cons_succ]
  have hpost (l r : ℕ) (s : State k) (u : Fin l → State k) (v : Fin r → State k)
      (i : Fin r) :
      (Fin.cons s (Fin.append u v) : Fin (l+r+1) → State k) (i.natAdd l).castSucc =
        (Fin.cons (endpoint l s u) v : Fin (r+1) → State k) i.castSucc := by
    cases r with
    | zero => exact Fin.elim0 i
    | succ r =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.castSucc_zero, Fin.cons_zero]
        rw [hend]
        cases l with
        | zero => simp
        | succ l =>
          have he : ((0 : Fin (r+1)).natAdd (l+1)).castSucc =
              ((Fin.last l).castAdd (r+1)).succ := by apply Fin.ext; simp
          rw [he, Fin.cons_succ, Fin.append_left, Fin.cons_last]
      · have he : (j.succ.natAdd l).castSucc = (j.castSucc.natAdd l).succ := by
          apply Fin.ext; simp; omega
        rw [he, Fin.cons_succ, Fin.append_right, ← Fin.succ_castSucc, Fin.cons_succ]
  have hrpre (l r : ℕ) (s : State k) (u : Fin l → State k) (v : Fin r → State k)
      (i : Fin l) : relations s (Fin.append u v) (i.castAdd r) = relations s u i := by
    simp only [relations, hpre, Fin.append_left]
  have hrpost (l r : ℕ) (s : State k) (u : Fin l → State k) (v : Fin r → State k)
      (i : Fin r) : relations s (Fin.append u v) (i.natAdd l) =
        relations (endpoint l s u) v i := by
    simp only [relations, hpost, Fin.append_right]
  have happ (l r : ℕ) (s : State k) (u : Fin l → State k) (v : Fin r → State k) :
      pathWeight k p (l+r) s (Fin.append u v) =
        pathWeight k p l s u * pathWeight k p r (endpoint l s u) v := by
    simp only [hprod, Fin.prod_univ_add, hpre, hpost, Fin.append_left, Fin.append_right]
  have hones {n : ℕ} (w : Fin n → Bool) (i : Fin n) :
      i.val ∈ windowOnes w ↔ w i = true := by
    simp only [windowOnes, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, he⟩
      have : j = i := Fin.ext he
      simpa [this] using hj
    · intro hi
      exact ⟨i, hi, rfl⟩
  have htailE (n : ℕ) (s : State k) (u : Fin 4 → State k) (v : Fin n → State k)
      (he : E (4+n) s (Fin.append u v)) : E n (endpoint 4 s u) v := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    obtain ⟨hcprod, _, hlen, hca, hcb, hcz⟩ := Finset.mem_filter.mp hc
    have ha' : c.1 < n := Finset.mem_range.mp (Finset.mem_product.mp hcprod).1
    have hb'' : c.2 < n := Finset.mem_range.mp (Finset.mem_product.mp hcprod).2
    have haBit := (hones (relations (endpoint 4 s u) v) ⟨c.1,ha'⟩).mp hca
    have hbBit := (hones (relations (endpoint 4 s u) v) ⟨c.2,hb''⟩).mp hcb
    have hshift (i : Fin n) :
        relations s (Fin.append u v) (i.natAdd 4) = relations (endpoint 4 s u) v i :=
      hrpost 4 n s u v i
    have hm : (4+c.1,4+c.2) ∈ candidates (windowOnes (relations s (Fin.append u v)))
        (4+n) (4+n) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩, by omega, by dsimp; omega, ?_, ?_, ?_⟩
      · exact (hones _ ((⟨c.1,ha'⟩ : Fin n).natAdd 4)).mpr ((hshift _).trans haBit)
      · exact (hones _ ((⟨c.2,hb''⟩ : Fin n).natAdd 4)).mpr ((hshift _).trans hbBit)
      · intro x hx hxb hxm
        have hxlo : 4 ≤ x := by omega
        let i : Fin n := ⟨x-4, by omega⟩
        have hi : i.natAdd 4 = (⟨x, by omega⟩ : Fin (4+n)) := by
          apply Fin.ext
          dsimp [i]
          omega
        have hbit := (hones (relations s (Fin.append u v)) ⟨x,by omega⟩).mp hxm
        rw [← hi, hshift] at hbit
        exact hcz i.val (by dsimp [i]; omega) (by dsimp [i]; omega)
          ((hones _ i).mpr hbit)
    rw [he] at hm
    exact Finset.notMem_empty _ hm
  let special (s : State k) : Fin 4 → State k :=
    ![(!s.1,z), (!s.1,o), (s.1,z), (s.1,o)]
  have hspecial_mass (s : State k) :
      (1/32 : ℝ) ≤ pathWeight k p 4 s (special s) := by
    have hsupport : 0 < pathWeight k p 4 s (special s) := by
      have hs : s.1 ≠ !s.1 := by cases s.1 <;> decide
      simp only [pathWeight, special, Matrix.cons_val_zero]
      simp [kernel, z, o, hz, hs, Ne.symm hs]
      have hsuf := hh s.2
      have hone := hh o
      dsimp [o] at hone
      positivity
    have he := (parry_word_mass k hk).1 4 s (special s) hsupport.ne'
    have hendpoint : (endpoint 4 s (special s)).2 = o := rfl
    rw [he, hendpoint]
    have hpow : (1/32 : ℝ) ≤ p^5 := by
      have ht := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hr.1.le 5
      norm_num at ht
      exact ht
    apply (le_div_iff₀ (hh s.2)).mpr
    have hlow := mul_le_mul_of_nonneg_left (hb o).1 (pow_nonneg hp.le 4)
    have hhigh := mul_le_mul_of_nonneg_left (hb s.2).2 (by norm_num : (0:ℝ) ≤ 1/32)
    nlinarith [show p^5 = p^4*p from pow_succ p 4]
  have hspecial_bad (n : ℕ) (s : State k) (v : Fin n → State k) :
      ¬ E (4+n) s (Fin.append (special s) v) := by
    intro he
    have hb1 : relations s (special s) 1 = true := by
      cases hs : s.1 <;> simp [relations, special, hs]
    have hb2 : relations s (special s) 2 = false := by
      cases hs : s.1 <;> simp [relations, special, hs]
    have hb3 : relations s (special s) 3 = true := by
      cases hs : s.1 <;> simp [relations, special, hs]
    have hm : (1,3) ∈ candidates (windowOnes (relations s (Fin.append (special s) v)))
        (4+n) (4+n) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩, by omega, by decide, ?_, ?_, ?_⟩
      · exact (hones _ ((1 : Fin 4).castAdd n)).mpr
          ((hrpre 4 n s (special s) v 1).trans hb1)
      · exact (hones _ ((3 : Fin 4).castAdd n)).mpr
          ((hrpre 4 n s (special s) v 3).trans hb3)
      · intro x hx hxb hxm
        have hx2 : x = 2 := by omega
        subst x
        have hbit := (hones _ ((2 : Fin 4).castAdd n)).mp hxm
        rw [hrpre, hb2] at hbit
        contradiction
    rw [he] at hm
    exact Finset.notMem_empty _ hm
  have havoids : ∀ (n : ℕ) (s : State k),
      (∑ v : Fin n → State k, if E n s v then pathWeight k p n s v else 0) ≤
        (31/32 : ℝ)^(n/4) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s
      by_cases hn : n < 4
      · rw [Nat.div_eq_of_lt hn, pow_zero, ← hrows n s]
        apply Finset.sum_le_sum
        intro v _
        split_ifs
        · exact le_rfl
        · exact hw n s v
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show 4 ≤ n by omega)
        have him (t : State k) := ih m (by omega) t
        rw [← Equiv.sum_comp (Fin.appendEquiv 4 m), Fintype.sum_prod_type]
        simp only [Fin.appendEquiv, Equiv.coe_fn_mk, happ]
        have hlocal (u : Fin 4 → State k) :
            (∑ v : Fin m → State k, if E (4+m) s (Fin.append u v) then
              pathWeight k p 4 s u * pathWeight k p m (endpoint 4 s u) v else 0) ≤
              if u = special s then 0 else pathWeight k p 4 s u * (31/32 : ℝ)^(m/4) := by
          by_cases hu : u = special s
          · subst u
            simp [hspecial_bad]
          · rw [if_neg hu]
            calc
              _ ≤ ∑ v : Fin m → State k,
                  pathWeight k p 4 s u *
                    (if E m (endpoint 4 s u) v then
                      pathWeight k p m (endpoint 4 s u) v else 0) := by
                apply Finset.sum_le_sum
                intro v _
                by_cases he : E (4+m) s (Fin.append u v)
                · rw [if_pos he, if_pos (htailE m s u v he)]
                · rw [if_neg he]
                  apply mul_nonneg (hw _ _ _)
                  split_ifs
                  · exact hw _ _ _
                  · exact le_rfl
              _ = pathWeight k p 4 s u *
                  (∑ v : Fin m → State k, if E m (endpoint 4 s u) v then
                    pathWeight k p m (endpoint 4 s u) v else 0) := (Finset.mul_sum ..).symm
              _ ≤ _ := mul_le_mul_of_nonneg_left (him _) (hw _ _ _)
        calc
          _ ≤ ∑ u : Fin 4 → State k,
              if u = special s then 0 else pathWeight k p 4 s u * (31/32 : ℝ)^(m/4) :=
            Finset.sum_le_sum fun u _ => hlocal u
          _ = (1 - pathWeight k p 4 s (special s)) * (31/32 : ℝ)^(m/4) := by
            have he (u : Fin 4 → State k) :
                (if u = special s then 0 else pathWeight k p 4 s u * (31/32 : ℝ)^(m/4)) =
                pathWeight k p 4 s u * (31/32 : ℝ)^(m/4) -
                (if u = special s then
                  pathWeight k p 4 s (special s) * (31/32 : ℝ)^(m/4) else 0) := by
              split_ifs with hu
              · subst u; ring
              · ring
            simp_rw [he]
            rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hrows]
            simp
            ring
          _ ≤ (31/32 : ℝ) * (31/32 : ℝ)^(m/4) :=
            mul_le_mul_of_nonneg_right (by linarith [hspecial_mass s]) (by positivity)
          _ = (31/32 : ℝ)^((4+m)/4) := by
            rw [show (4+m)/4 = m/4+1 by omega, pow_succ]
            ring
  refine ⟨?_, ?_⟩
  · intro s
    simpa only [Finset.sum_filter] using havoids R s
  · have hevent (s t : State k) (v : Fin R → State k) :
        selected (windowOnes (fun i : Fin R =>
          prefixRelation (s, Fin.cons t v) i.succ)) R R = none ↔ E R t v := by
      have he : (fun i : Fin R => prefixRelation (s, Fin.cons t v) i.succ) =
          relations t v := by
        funext i
        simp only [prefixRelation, relations, ← Fin.succ_castSucc, Fin.cons_succ]
      rw [he]
      simp [selected, List.argmax_eq_none, E]
    have hcond (s : State k) :
        (∑ u : Fin (R+1) → State k,
          if selected (windowOnes (fun i : Fin R => prefixRelation (s,u) i.succ)) R R = none
          then pathWeight k p (R+1) s u else 0) ≤ (31/32 : ℝ)^(R/4) := by
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (R+1) => State k),
        Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, hevent, pathWeight,
        Fin.cons_zero, Fin.cons_succ]
      calc
        _ = ∑ t : State k, kernel k p s t *
            (∑ v : Fin R → State k, if E R t v then pathWeight k p R t v else 0) := by
          simp only [Finset.mul_sum, mul_ite, mul_zero]
        _ ≤ ∑ t : State k, kernel k p s t * (31/32 : ℝ)^(R/4) :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (havoids R t) (hQ s t)
        _ = _ := by rw [← Finset.sum_mul, hrow]; ring
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    change (∑ s : State k, ∑ u : Fin (R+1) → State k,
      if selected (windowOnes (fun i : Fin R => prefixRelation (s,u) i.succ)) R R = none
      then parryLaw k s * pathWeight k p (R+1) s u else 0) ≤ _
    calc
      _ = ∑ s : State k, parryLaw k s *
          (∑ u : Fin (R+1) → State k,
            if selected (windowOnes (fun i : Fin R => prefixRelation (s,u) i.succ)) R R = none
            then pathWeight k p (R+1) s u else 0) := by
        simp only [Finset.mul_sum, mul_ite, mul_zero]
      _ ≤ ∑ s : State k, parryLaw k s * (31/32 : ℝ)^(R/4) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hcond s) (hπ s)
      _ = _ := by rw [← Finset.sum_mul, hπsum]; ring

#print axioms parry_complete_run_laws
#print axioms parry_no_complete_run_bound

end D5.S3.TotalVariation.ParrySharedZeroRule
