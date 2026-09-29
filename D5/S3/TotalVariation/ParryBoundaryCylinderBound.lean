/- GID: D5/S3/TotalVariation/ParryBoundaryCylinderBound
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParryBoundaryCylinderBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite run cylinders bound both boundary selections under the actual Parry law. -/

import D5.S3.TotalVariation.ParryRunPrefixCode

open scoped BigOperators
open D5.S3.ObserverMemory.Trajectories.LongestZeroSelectorResponse
open D5.S3.ObserverMemory.Trajectories.ZeroRunWordGeometry
open D5.S3.TotalVariation.TwistedResetPaths
open D5.S3.TotalVariation.TwistedPrefixComparison
open D5.S3.TotalVariation.ParryResetLaw
open D5.S3.TotalVariation.ParryWordCollision
open D5.S3.TotalVariation.ParrySharedZeroRule
open D5.S3.TotalVariation.ParryRunPrefixCode

namespace D5.S3.TotalVariation.ParryBoundaryCylinderBound

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

/-- Every finite family of fitting codes with a fixed positive run count gives
both boundary estimates for the original longest-complete-run selector.
The first run may tie for the maximum. All masses are actual stationary
finite signed-state path sums; no law or containment premise is assumed. -/
theorem parry_boundary_cylinder_bound (k : ℕ) (hk : 2 ≤ k) (R n : ℕ)
    (hn : 1 ≤ n) (C : Finset (List (ℕ × ℕ)))
    (hlen : ∀ cs ∈ C, cs.length = n)
    (hvalid : ∀ cs ∈ C, ∀ c ∈ cs, 1 ≤ c.1 ∧ 1 ≤ c.2 ∧ c.2 < k)
    (hfit : ∀ cs ∈ C, 2 + (cs.map (fun c => c.1 + c.2)).sum ≤ R) :
    let p := parryParameter k
    let S := ∑ cs ∈ C, p ^ (cs.map (fun c => c.1 + c.2)).sum
    let M := ∑ cs ∈ C with ∀ c ∈ cs, c.1 ≤ (cs.headD (0, 0)).1,
      p ^ (cs.map (fun c => c.1 + c.2)).sum
    (∑ v : Prefix k R with ∃ c, selected (windowOnes (relations v.1 v.2)) R R =
        some c ∧ c.1 = 0, referenceLaw k p R (parryLaw k) v) ≤
      stationaryWordMass k [true, false] * (1 - S + M) ∧
    (∑ v : Prefix k R with ∃ c, selected (windowOnes (relations v.1 v.2)) R R =
        some c ∧ c.2 = R - 1, referenceLaw k p R (parryLaw k) v) ≤
      stationaryWordMass k [false, true] * (1 - S + M) := by
  classical
  let p := parryParameter k
  let π := parryLaw k
  let code (cs : List (ℕ × ℕ)) := [true, false] ++ runContinuation cs
  let size (cs : List (ℕ × ℕ)) := (cs.map (fun c => c.1 + c.2)).sum
  let maximal (cs : List (ℕ × ℕ)) := ∀ c ∈ cs, c.1 ≤ (cs.headD (0, 0)).1
  obtain ⟨hr, _, _, hQ, hrow, hπ, _, hstat, _⟩ := parry_stationary_law k hk
  have hp : 0 < p := by dsimp [p]; linarith [hr.1]
  have hp1 : p < 1 := lt_of_le_of_lt hr.2.1
    (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
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
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (m + 1) => State k),
        Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, pathWeight, Fin.cons_zero, Fin.cons_succ]
      simp_rw [← Finset.mul_sum, ih, mul_one]
      exact hrow s
  have hstationary : ∀ (m : ℕ) (F : State k → ℝ),
      (∑ s : State k, ∑ v : Fin m → State k,
        π s * pathWeight k p m s v * F (endpoint m s v)) = ∑ t, π t * F t := by
    intro m
    induction m with
    | zero => intro F; simp [pathWeight, endpoint]
    | succ m ih =>
      intro F
      have hsplit (s : State k) :
          (∑ v : Fin (m + 1) → State k,
            π s * pathWeight k p (m + 1) s v * F (endpoint (m + 1) s v)) =
          ∑ t : State k, ∑ v : Fin m → State k,
            π s * (kernel k p s t * pathWeight k p m t v) * F (endpoint m t v) := by
        rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (m + 1) => State k),
          Fintype.sum_prod_type]
        rfl
      simp_rw [hsplit]
      rw [Finset.sum_comm]
      calc
        _ = ∑ t : State k, ∑ v : Fin m → State k,
            (∑ s : State k, π s * kernel k p s t) *
              pathWeight k p m t v * F (endpoint m t v) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.sum_comm]
          simp only [Finset.sum_mul]
          congr 1
          funext v
          apply Finset.sum_congr rfl
          intro s _
          ring
        _ = _ := by
          have hs (t : State k) : (∑ s, π s * kernel k p s t) = π t := hstat t
          simp_rw [hs]
          exact ih F
  have hend : ∀ (l : ℕ) (s : State k) (v : Fin l → State k),
      endpoint l s v = (Fin.cons s v : Fin (l + 1) → State k) (Fin.last l) := by
    intro l
    induction l with
    | zero => intro s v; rfl
    | succ l ih =>
      intro s v
      have hv : (Fin.cons (v 0) (fun i : Fin l => v i.succ) : Fin (l + 1) → State k) = v :=
        Fin.cons_self_tail v
      rw [endpoint, ih, hv, Fin.cons_last]
  have hprod : ∀ (l : ℕ) (s : State k) (v : Fin l → State k),
      pathWeight k p l s v = ∏ i : Fin l,
        kernel k p ((Fin.cons s v : Fin (l + 1) → State k) i.castSucc) (v i) := by
    intro l
    induction l with
    | zero => intro s v; simp [pathWeight]
    | succ l ih =>
      intro s v
      have hv : (Fin.cons (v 0) (fun i : Fin l => v i.succ) : Fin (l + 1) → State k) = v :=
        Fin.cons_self_tail v
      rw [pathWeight, ih, hv, Fin.prod_univ_succ]
      simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]
  have hpre (l r : ℕ) (s : State k) (u : Fin l → State k) (v : Fin r → State k)
      (i : Fin l) :
      (Fin.cons s (Fin.append u v) : Fin (l + r + 1) → State k) (i.castAdd r).castSucc =
        (Fin.cons s u : Fin (l + 1) → State k) i.castSucc := by
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
      (Fin.cons s (Fin.append u v) : Fin (l + r + 1) → State k) (i.natAdd l).castSucc =
        (Fin.cons (endpoint l s u) v : Fin (r + 1) → State k) i.castSucc := by
    cases r with
    | zero => exact Fin.elim0 i
    | succ r =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.castSucc_zero, Fin.cons_zero]
        rw [hend]
        cases l with
        | zero => simp
        | succ l =>
          have he : ((0 : Fin (r + 1)).natAdd (l + 1)).castSucc =
              ((Fin.last l).castAdd (r + 1)).succ := by apply Fin.ext; simp
          rw [he, Fin.cons_succ, Fin.append_left, Fin.cons_last]
      · have he : (j.succ.natAdd l).castSucc = (j.castSucc.natAdd l).succ := by
          apply Fin.ext; simp; omega
        rw [he, Fin.cons_succ, Fin.append_right, ← Fin.succ_castSucc, Fin.cons_succ]
  have happ (l r : ℕ) (s : State k) (u : Fin l → State k) (v : Fin r → State k) :
      pathWeight k p (l + r) s (Fin.append u v) =
        pathWeight k p l s u * pathWeight k p r (endpoint l s u) v := by
    simp only [hprod, Fin.prod_univ_add, hpre, hpost, Fin.append_left, Fin.append_right]
  have hrelapp (l r : ℕ) (s : State k) (u : Fin l → State k) (v : Fin r → State k) :
      List.ofFn (relations s (Fin.append u v)) = List.ofFn (relations s u) ++
        List.ofFn (relations (endpoint l s u) v) := by
    rw [List.ofFn_add]
    congr 1 <;> congr 1 <;> funext i
    · change relations s (Fin.append u v) (i.castAdd r) = relations s u i
      simp only [relations, hpre, Fin.append_left]
    · simp only [relations, hpost, Fin.append_right]
  have hpref (a b w : List Bool) (ha : a.length = w.length) :
      w.IsPrefix (a ++ b) ↔ a = w := by
    rw [List.prefix_iff_eq_take, ← ha, List.take_left]
    exact eq_comm
  have hpref_rev (a b w : List Bool) (ha : a.length = w.length) :
      w.reverse.IsPrefix (a.reverse ++ b) ↔ a = w := by
    rw [hpref _ _ _ (by simpa using ha), List.reverse_inj]
  have hmarginal (w : List Bool) (hwr : w.length ≤ R) :
      (∑ v : Prefix k R, if w.IsPrefix (List.ofFn (relations v.1 v.2)) then
        referenceLaw k p R π v else 0) = stationaryWordMass k w ∧
      (∑ v : Prefix k R, if w.reverse.IsPrefix (List.ofFn (relations v.1 v.2)).reverse
        then referenceLaw k p R π v else 0) = stationaryWordMass k w := by
    obtain ⟨d, hR⟩ := Nat.exists_eq_add_of_le hwr
    constructor
    · subst R
      rw [Fintype.sum_prod_type]
      conv_lhs => arg 2; ext s
                  rw [← Equiv.sum_comp (Fin.appendEquiv w.length d), Fintype.sum_prod_type]
      simp only [Fin.appendEquiv, Equiv.coe_fn_mk, hrelapp, referenceLaw, happ,
        hpref _ _ w List.length_ofFn]
      have hs (s : State k) (u : Fin w.length → State k) :
          (∑ v : Fin d → State k,
            if List.ofFn (relations s u) = w then
              π s * (pathWeight k p w.length s u *
                pathWeight k p d (endpoint w.length s u) v) else 0) =
            if List.ofFn (relations s u) = w then π s * pathWeight k p w.length s u else 0 := by
        split_ifs with h
        · simp only [← mul_assoc, ← Finset.mul_sum, hrows, mul_one]
        · simp
      simp_rw [hs]
      simp only [stationaryWordMass, Finset.sum_filter, Fintype.sum_prod_type, referenceLaw]
      rfl
    · have hR' : R = d + w.length := by omega
      rw [hR', Fintype.sum_prod_type]
      conv_lhs => arg 2; ext s
                  rw [← Equiv.sum_comp (Fin.appendEquiv d w.length), Fintype.sum_prod_type]
      simp only [Fin.appendEquiv, Equiv.coe_fn_mk, hrelapp, referenceLaw, happ,
        List.reverse_append, hpref_rev _ _ w List.length_ofFn]
      let F (t : State k) := ∑ v : Fin w.length → State k,
        if List.ofFn (relations t v) = w then pathWeight k p w.length t v else 0
      calc
        _ = ∑ s : State k, ∑ u : Fin d → State k,
            π s * pathWeight k p d s u * F (endpoint d s u) := by
          simp only [F, Finset.mul_sum, mul_ite, mul_zero]
          apply Finset.sum_congr rfl
          intro s _
          apply Finset.sum_congr rfl
          intro u _
          apply Finset.sum_congr rfl
          intro v _
          split_ifs <;> ring
        _ = ∑ t, π t * F t := hstationary d F
        _ = _ := by
          simp only [F, stationaryWordMass, Finset.sum_filter, Fintype.sum_prod_type,
            referenceLaw, Finset.mul_sum, mul_ite, mul_zero]
          rfl
  have hcodelen (cs : List (ℕ × ℕ))
      (hc : ∀ c ∈ cs, 1 ≤ c.1 ∧ 1 ≤ c.2) : (code cs).length = 2 + size cs := by
    have he : (runContinuation cs).length = size cs := by
      induction cs with
      | nil => simp [runContinuation, size]
      | cons c cs ih =>
        have h := hc c (by simp)
        have ht := ih (fun a ha => hc a (by simp [ha]))
        simp only [runContinuation, List.flatMap_cons, List.length_append,
          List.length_replicate, List.length_cons, List.length_nil, size,
          List.map_cons, List.sum_cons] at *
        omega
    simp only [code, List.length_append, List.length_cons, List.length_nil]
    omega
  have hcode_mass (cs : List (ℕ × ℕ)) (hc : ∀ c ∈ cs,
      1 ≤ c.1 ∧ 1 ≤ c.2 ∧ c.2 < k) :
      stationaryWordMass k (code cs) = stationaryWordMass k [true, false] * p ^ size cs ∧
      stationaryWordMass k (code cs).reverse = stationaryWordMass k [false, true] * p ^ size cs := by
    have hbase := parry_complete_run_laws k hk [] (by simp)
    have hprod : (cs.map (fun c => ((1 - p) * p ^ (c.1 - 1)) *
        (p ^ (c.2 + 1) / (1 - p)))).prod = p ^ size cs := by
      induction cs with
      | nil => simp [size]
      | cons c cs ih =>
        have hz := (hc c (by simp)).1
        have ht := ih (fun a ha => hc a (by simp [ha]))
        simp only [List.map_cons, List.prod_cons, size, List.sum_cons] at *
        rw [ht]
        have hf : ((1 - p) * p ^ (c.1 - 1)) * (p ^ (c.2 + 1) / (1 - p)) =
            p ^ (c.1 + c.2) := by
          field_simp [show 1 - p ≠ 0 by linarith]
          rw [← pow_add, show c.1 - 1 + (c.2 + 1) = c.1 + c.2 by omega]
        rw [hf, ← pow_add]
    have hm := parry_complete_run_laws k hk cs hc
    have hb0 : stationaryWordMass k [true, false] ≠ 0 := by
      intro hz
      simpa [runContinuation, hz] using hbase.1
    have hb1 : stationaryWordMass k [false, true] ≠ 0 := by
      intro hz
      simpa [runContinuation, hz] using hbase.2
    change stationaryWordMass k (code cs) / stationaryWordMass k [true, false] = _ ∧
      stationaryWordMass k (code cs).reverse / stationaryWordMass k [false, true] = _ at hm
    rw [hprod] at hm
    exact ⟨by nlinarith [(div_eq_iff hb0).mp hm.1],
      by nlinarith [(div_eq_iff hb1).mp hm.2]⟩

  let gaps (cs : List (ℕ × ℕ)) := cs.flatMap fun c => c.1 :: List.replicate (c.2 - 1) 0
  let gapword (ls : List ℕ) := true :: ls.flatMap (fun l => List.replicate l false ++ [true])
  have hgaplen (ls : List ℕ) : (gapword ls).length = span ls + 1 := by
    simp only [gapword, List.length_cons, List.length_flatMap, span]
    congr 1
    congr 1
    apply List.map_congr_left
    intro l _
    simp
  have hzeros (m : ℕ) :
      (List.replicate m 0).flatMap (fun l => List.replicate l false ++ [true]) =
        List.replicate m true := by
    induction m with
    | zero => rfl
    | succ m ih => simpa [List.replicate_succ] using congrArg (true :: ·) ih
  have hcodegap (cs : List (ℕ × ℕ))
      (hc : ∀ c ∈ cs, 1 ≤ c.1 ∧ 1 ≤ c.2) : code cs = gapword (gaps cs) ++ [false] := by
    have haux : false :: runContinuation cs =
        (gaps cs).flatMap (fun l => List.replicate l false ++ [true]) ++ [false] := by
      induction cs with
      | nil => rfl
      | cons c cs ih =>
        obtain ⟨hz, ho⟩ := hc c (by simp)
        have ht := ih (fun a ha => hc a (by simp [ha]))
        have hez : c.1 - 1 + 1 = c.1 := by omega
        have heo : c.2 - 1 + 1 = c.2 := by omega
        change false :: ((List.replicate (c.1 - 1) false ++
          List.replicate c.2 true ++ [false]) ++ runContinuation cs) = _
        rw [List.append_assoc, List.append_assoc]
        change (false :: List.replicate (c.1 - 1) false) ++
          (List.replicate c.2 true ++ false :: runContinuation cs) = _
        rw [← List.replicate_succ, hez, ht]
        simp only [gaps, List.flatMap_cons, List.flatMap_append, List.flatMap_cons,
          hzeros, List.singleton_append, List.append_assoc]
        rw [← List.replicate_succ, heo]
    simpa [code, gapword] using congrArg (true :: ·) haux
  have honesget : ∀ (ls : List ℕ) (a x : ℕ),
      x ∈ ones ls a ↔ (List.replicate a false ++ gapword ls)[x]? = some true := by
    intro ls
    induction ls with
    | nil =>
      intro a x
      simp only [ones, Finset.mem_singleton, gapword, List.flatMap_nil,
        List.getElem?_append, List.length_replicate]
      by_cases hx : x < a
      · simp [hx, List.getElem?_replicate, show x ≠ a by omega]
      · simp [hx, List.getElem?_cons] <;> omega
    | cons l ls ih =>
      intro a x
      simp only [ones, Finset.mem_insert, ih, gapword, List.flatMap_cons,
        List.cons_append, List.singleton_append, List.append_assoc]
      by_cases hx : x < a
      · simp [List.getElem?_append, List.getElem?_replicate, hx,
          show x < a + l + 1 by omega, show x ≠ a by omega]
      · by_cases hxa : x = a
        · subst x
          simp [List.getElem?_append, List.getElem?_replicate]
        · have hxpos : 0 < x - a := by omega
          simp only [List.getElem?_append, List.length_replicate,
            List.getElem?_cons, if_neg hx, if_neg (by omega : x - a ≠ 0)]
          by_cases hxl : x < a + l + 1
          · simp [hxl, List.getElem?_replicate, show x - a - 1 < l by omega, hxa]
          · simp [hxl, List.getElem?_replicate, show ¬ x - a - 1 < l by omega,
              hxa, show x - (a + l + 1) = x - a - 1 - l by omega]
  have hwindow {m : ℕ} (w : Fin m → Bool) (i : Fin m) :
      i.val ∈ windowOnes w ↔ w i = true := by
    simp only [windowOnes, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, he⟩
      have : j = i := Fin.ext he
      simpa [this] using hj
    · intro hi
      exact ⟨i, hi, rfl⟩
  have hrealize (cs : List (ℕ × ℕ))
      (hc : ∀ c ∈ cs, 1 ≤ c.1 ∧ 1 ≤ c.2) (w : Fin R → Bool)
      (hpre : (code cs).IsPrefix (List.ofFn w)) :
      ∀ c ∈ intervals (gaps cs) 0,
        Complete (windowOnes w) c.1 c.2 ∧ c.2 < R := by
    have hpref : (gapword (gaps cs)).IsPrefix (List.ofFn w) := by
      rw [hcodegap cs hc] at hpre
      exact (List.prefix_append _ _).trans hpre
    have hagree (x : ℕ) (hx : x ≤ span (gaps cs)) :
        x ∈ windowOnes w ↔ x ∈ ones (gaps cs) 0 := by
      have hxg : x < (gapword (gaps cs)).length := by rw [hgaplen]; omega
      have hxr : x < R := by have := hpref.length_le; simp only [List.length_ofFn] at this; omega
      rw [hwindow w ⟨x, hxr⟩, honesget]
      simp only [List.replicate_zero, List.nil_append]
      rw [List.getElem?_eq_getElem hxg, hpref.getElem hxg, List.getElem_ofFn]
      simp
    intro c hcint
    obtain ⟨_, hab, hbe, _⟩ := (interval_geometry (gaps cs) 0).1 c hcint
    obtain ⟨_, ha, hb, hz⟩ := (complete_iff_interval (gaps cs) 0 c.1 c.2).mpr hcint
    refine ⟨⟨hab, (hagree c.1 (by omega)).mpr ha,
      (hagree c.2 (by omega)).mpr hb, ?_⟩, ?_⟩
    · intro x hax hxb hx
      exact hz x hax hxb ((hagree x (by omega)).mp hx)
    · have hle := hpref.length_le
      rw [hgaplen, List.length_ofFn] at hle
      omega
  have hgapruns : ∀ (cs : List (ℕ × ℕ)) (a : ℕ),
      (∀ c ∈ cs, 1 ≤ c.1 ∧ 1 ≤ c.2) →
      ∀ c ∈ cs, ∃ d ∈ intervals (gaps cs) a, d.2 - d.1 - 1 = c.1 := by
    intro cs
    induction cs with
    | nil => simp
    | cons c cs ih =>
      intro a hc d hd
      obtain ⟨hz, ho⟩ := hc c (by simp)
      have hi := (interval_geometry (c.1 :: List.replicate (c.2 - 1) 0) a).2 (gaps cs)
      change intervals (gaps (c :: cs)) a = _ at hi
      rw [hi]
      rcases List.mem_cons.mp hd with hd | hd
      · subst d
        refine ⟨(a, a + c.1 + 1), Finset.mem_union_left _ ?_, by dsimp; omega⟩
        simp [intervals, show 0 < c.1 by omega]
      · obtain ⟨e, he, hel⟩ := ih _ (fun b hb => hc b (by simp [hb])) d hd
        exact ⟨e, Finset.mem_union_right _ he, hel⟩
  have hhead (c : ℕ × ℕ) (cs : List (ℕ × ℕ)) (hc : 1 ≤ c.1) :
      (0, c.1 + 1) ∈ intervals (gaps (c :: cs)) 0 := by
    simp [gaps, List.flatMap_cons, intervals, show 0 < c.1 by omega]
  have hunique (s : Finset ℕ) (a b d : ℕ)
      (hb : Complete s a b) (hd : Complete s a d) : b = d := by
    have hb0 := hb.1
    have hd0 := hd.1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hd.2.2.2 b (by omega) hlt hb.2.2.1
    · exact hb.2.2.2 d (by omega) hgt hd.2.2.1
  have hforce (cs : List (ℕ × ℕ)) (hcs : cs ∈ C) (w : Fin R → Bool)
      (hpre : (code cs).IsPrefix (List.ofFn w)) (b : ℕ)
      (hb : Complete (windowOnes w) 0 b)
      (hmax : ∀ d : ℕ × ℕ, Complete (windowOnes w) d.1 d.2 → d.2 < R →
        d.2 - d.1 - 1 ≤ b - 1) : maximal cs := by
    have hc : ∀ c ∈ cs, 1 ≤ c.1 ∧ 1 ≤ c.2 :=
      fun c hm => ⟨(hvalid cs hcs c hm).1, (hvalid cs hcs c hm).2.1⟩
    have hruns := hrealize cs hc w hpre
    have hlength := hlen cs hcs
    cases cs with
    | nil => simp at hlength; omega
    | cons c cs =>
      have hz := (hc c (by simp)).1
      have hfirst := hruns (0, c.1 + 1) (hhead c cs hz)
      have hbeq := hunique (windowOnes w) 0 b (c.1 + 1) hb hfirst.1
      intro d hd
      obtain ⟨e, he, hel⟩ := hgapruns (c :: cs) 0 hc d hd
      have he' := hruns e he
      have hh := hmax e he'.1 he'.2
      simpa [hbeq, hel, List.headD_cons] using hh

  have hselected (w : Fin R → Bool) (c : ℕ × ℕ)
      (hs : selected (windowOnes w) R R = some c) :
      Complete (windowOnes w) c.1 c.2 ∧ c.2 < R ∧
      ∀ d : ℕ × ℕ, Complete (windowOnes w) d.1 d.2 → d.2 < R →
        d.2 - d.1 - 1 ≤ c.2 - c.1 - 1 := by
    obtain ⟨hm, hmax, _⟩ := List.argmax_eq_some_iff.mp hs
    obtain ⟨hi, _, hc⟩ := Finset.mem_filter.mp (Finset.mem_toList.mp hm)
    have hb := Finset.mem_range.mp (Finset.mem_product.mp hi).2
    refine ⟨hc, hb, ?_⟩
    intro d hd hdb
    have hda : d.1 < R := by have := hd.1; omega
    have hdm : d ∈ candidates (windowOnes w) R R := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hda, Finset.mem_range.mpr hdb⟩, by omega, hd⟩
    have hscore := hmax d (Finset.mem_toList.mpr hdm)
    dsimp [score] at hscore
    by_contra hnle
    have hh : c.2 - c.1 - 1 + 1 ≤ d.2 - d.1 - 1 := by omega
    nlinarith only [hscore, hb, hh]
  have hrev (w : Fin R → Bool) (x : ℕ) (hx : x < R) :
      x ∈ windowOnes (fun i => w i.rev) ↔ R - 1 - x ∈ windowOnes w := by
    have he : (⟨x, hx⟩ : Fin R).rev.val = R - 1 - x := by simp [Fin.rev]; omega
    rw [← he, hwindow w (⟨x, hx⟩ : Fin R).rev, hwindow _ ⟨x, hx⟩]
  have hreflect (w : Fin R → Bool) (a b : ℕ) (hb : b < R)
      (hc : Complete (windowOnes w) a b) :
      Complete (windowOnes (fun i => w i.rev)) (R - 1 - b) (R - 1 - a) := by
    have hab := hc.1
    have ha : a < R := by omega
    have hR : 0 < R := by omega
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [hrev w _ (by omega), show R - 1 - (R - 1 - b) = b by omega]
      exact hc.2.2.1
    · rw [hrev w _ (by omega), show R - 1 - (R - 1 - a) = a by omega]
      exact hc.2.1
    · intro x hax hxb hx
      have hxR : x < R := by omega
      have hm := (hrev w x hxR).mp hx
      exact hc.2.2.2 (R - 1 - x) (by omega) (by omega) hm
  have hboundary (w : Fin R → Bool) (b : ℕ) (hb : b < R)
      (hc : Complete (windowOnes w) 0 b) : [true, false].IsPrefix (List.ofFn w) := by
    have hlen := hc.1
    have h0 : w ⟨0, by omega⟩ = true := (hwindow w ⟨0, by omega⟩).mp hc.2.1
    have h1 : w ⟨1, by omega⟩ = false := by
      have hz := hc.2.2.2 1 (by omega) (by omega)
      have hnot : w ⟨1, by omega⟩ ≠ true := fun h => hz ((hwindow w _).mpr h)
      cases he : w ⟨1, by omega⟩ with
      | false => rfl
      | true => exact (hnot he).elim
    apply List.prefix_iff_getElem.mpr
    refine ⟨by simp; omega, ?_⟩
    intro i hi
    have hi2 : i < 2 := by simpa using hi
    interval_cases i <;> simp [List.getElem_ofFn, h0, h1]
  have hrevword (w : Fin R → Bool) : List.ofFn (fun i => w i.rev) = (List.ofFn w).reverse := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
      congr 1
      apply Fin.ext
      change R - (i + 1) = R - 1 - i
      omega
  let oriented (rev : Bool) (w : Fin R → Bool) : Fin R → Bool :=
    if rev then fun i => w i.rev else w
  let event (rev : Bool) (v : Prefix k R) := ∃ c,
    selected (windowOnes (relations v.1 v.2)) R R = some c ∧
      if rev then c.2 = R - 1 else c.1 = 0
  let cylinder (rev : Bool) (cs : List (ℕ × ℕ)) (v : Prefix k R) :=
    (code cs).IsPrefix (List.ofFn (oriented rev (relations v.1 v.2)))
  let boundary (rev : Bool) (v : Prefix k R) :=
    [true, false].IsPrefix (List.ofFn (oriented rev (relations v.1 v.2)))
  let β (rev : Bool) := if rev then stationaryWordMass k [false, true]
    else stationaryWordMass k [true, false]
  let P := referenceLaw k p R π
  have hP (v : Prefix k R) : 0 ≤ P v := mul_nonneg (hπ _) (hw _ _ _)
  have hβ (rev : Bool) : 0 ≤ β rev := by
    have hm (w : List Bool) : 0 ≤ stationaryWordMass k w :=
      Finset.sum_nonneg fun v _ => mul_nonneg (hπ _) (hw _ _ _)
    cases rev <;> exact hm _
  have hevent (rev : Bool) (v : Prefix k R) (he : event rev v) :
      boundary rev v ∧ ∀ cs ∈ C, cylinder rev cs v → maximal cs := by
    obtain ⟨c, hs, hb⟩ := he
    obtain ⟨hc, hcR, hmax⟩ := hselected _ c hs
    cases rev with
    | false =>
      change c.1 = 0 at hb
      have hc0 : Complete (windowOnes (relations v.1 v.2)) 0 c.2 := by simpa [hb] using hc
      refine ⟨hboundary _ c.2 hcR hc0, ?_⟩
      intro cs hcs hpre
      apply hforce cs hcs _ hpre c.2 hc0
      intro d hd hdR
      simpa [hb] using hmax d hd hdR
    | true =>
      change c.2 = R - 1 at hb
      have hca := hc.1
      have haR : c.1 < R := by omega
      have hrc : Complete (windowOnes (fun i => relations v.1 v.2 i.rev))
          0 (R - 1 - c.1) := by
        simpa [hb] using hreflect _ c.1 c.2 hcR hc
      refine ⟨hboundary _ _ (by omega) hrc, ?_⟩
      intro cs hcs hpre
      apply hforce cs hcs _ hpre (R - 1 - c.1) hrc
      intro d hd hdR
      have hda := hd.1
      have hrd := hreflect (fun i => relations v.1 v.2 i.rev) d.1 d.2 hdR hd
      simp only [Fin.rev_rev] at hrd
      have hh := hmax (R - 1 - d.2, R - 1 - d.1) hrd (by dsimp; omega)
      dsimp at hh
      omega
  have hdisjoint (rev : Bool) (v : Prefix k R) (cs ds : List (ℕ × ℕ))
      (hcs : cs ∈ C) (hds : ds ∈ C) (hc : cylinder rev cs v) (hd : cylinder rev ds v) : cs = ds := by
    have hcpos : ∀ c ∈ cs, 1 ≤ c.1 ∧ 1 ≤ c.2 :=
      fun c hm => ⟨(hvalid cs hcs c hm).1, (hvalid cs hcs c hm).2.1⟩
    have hdpos : ∀ d ∈ ds, 1 ≤ d.1 ∧ 1 ≤ d.2 :=
      fun d hm => ⟨(hvalid ds hds d hm).1, (hvalid ds hds d hm).2.1⟩
    rcases List.prefix_or_prefix_of_prefix hc hd with h | h
    · exact (run_word_prefix_iff cs ds ((hlen cs hcs).trans (hlen ds hds).symm)
        hcpos hdpos).mp h
    · exact ((run_word_prefix_iff ds cs ((hlen ds hds).trans (hlen cs hcs).symm)
        hdpos hcpos).mp h).symm
  have hcylinder_boundary (rev : Bool) (cs : List (ℕ × ℕ)) (v : Prefix k R)
      (hc : cylinder rev cs v) : boundary rev v := (List.prefix_append _ _).trans hc
  have hcylinder_mass (rev : Bool) (cs : List (ℕ × ℕ)) (hc : cs ∈ C) :
      (∑ v : Prefix k R, if cylinder rev cs v then P v else 0) = β rev * p ^ size cs := by
    have hsize : (code cs).length ≤ R := by
      rw [hcodelen cs (fun c hm => ⟨(hvalid cs hc c hm).1, (hvalid cs hc c hm).2.1⟩)]
      exact hfit cs hc
    cases rev with
    | false =>
      exact (hmarginal (code cs) hsize).1.trans (hcode_mass cs (hvalid cs hc)).1
    | true =>
      have hm := (hmarginal (code cs).reverse (by simpa using hsize)).2
      simpa [cylinder, oriented, P, β, hrevword] using
        hm.trans (hcode_mass cs (hvalid cs hc)).2
  have hboundary_mass (rev : Bool) :
      (∑ v : Prefix k R, if boundary rev v then P v else 0) ≤ β rev := by
    by_cases hR : 2 ≤ R
    · cases rev with
      | false => exact ((hmarginal [true, false] (by simpa using hR)).1).le
      | true =>
        have hm := (hmarginal [false, true] (by simpa using hR)).2
        exact (by simpa [boundary, oriented, P, β, hrevword] using hm.le)
    · have hnob (v : Prefix k R) : ¬ boundary rev v := by
        intro hb
        have hh := hb.length_le
        simp only [List.length_cons, List.length_nil, List.length_ofFn] at hh
        omega
      simpa only [hnob, if_false, Finset.sum_const_zero] using hβ rev
  have hbound (rev : Bool) :
      (∑ v : Prefix k R, if event rev v then P v else 0) ≤
        β rev * (1 - ∑ cs ∈ C, p ^ size cs + ∑ cs ∈ C with maximal cs, p ^ size cs) := by
    have hpoint (v : Prefix k R) : (if event rev v then P v else 0) ≤
        (if boundary rev v then P v else 0) -
          (∑ cs ∈ C, if cylinder rev cs v then P v else 0) +
          ∑ cs ∈ C with maximal cs, if cylinder rev cs v then P v else 0 := by
      by_cases hex : ∃ cs ∈ C, cylinder rev cs v
      · obtain ⟨a, ha, hav⟩ := hex
        have hz (cs : List (ℕ × ℕ)) (hcs : cs ∈ C) (hne : cs ≠ a) :
            ¬ cylinder rev cs v := fun hc => hne (hdisjoint rev v cs a hcs ha hc hav)
        have hs : (∑ cs ∈ C, if cylinder rev cs v then P v else 0) = P v := by
          rw [Finset.sum_eq_single a]
          · simp [hav]
          · intro cs hcs hne; simp [hz cs hcs hne]
          · simp [ha]
        have hms : (∑ cs ∈ C with maximal cs, if cylinder rev cs v then P v else 0) =
            if maximal a then P v else 0 := by
          by_cases hm : maximal a
          · rw [if_pos hm, Finset.sum_eq_single a]
            · simp [hav]
            · intro cs hcs hne; simp [hz cs (Finset.mem_filter.mp hcs).1 hne]
            · simp [ha, hm]
          · rw [if_neg hm]
            apply Finset.sum_eq_zero
            intro cs hcs
            have hne : cs ≠ a := by
              intro he; subst cs; exact hm (Finset.mem_filter.mp hcs).2
            simp [hz cs (Finset.mem_filter.mp hcs).1 hne]
        rw [hs, hms, if_pos (hcylinder_boundary rev a v hav), sub_self, zero_add]
        by_cases he : event rev v
        · simp [he, (hevent rev v he).2 a ha hav]
        · rw [if_neg he]
          split_ifs <;> first | exact hP v | exact le_rfl
      · have hz (cs : List (ℕ × ℕ)) (hc : cs ∈ C) : ¬ cylinder rev cs v :=
          fun h => hex ⟨cs, hc, h⟩
        have hs : (∑ cs ∈ C, if cylinder rev cs v then P v else 0) = 0 :=
          Finset.sum_eq_zero fun cs hc => if_neg (hz cs hc)
        have hms : (∑ cs ∈ C with maximal cs, if cylinder rev cs v then P v else 0) = 0 :=
          Finset.sum_eq_zero fun cs hc => if_neg (hz cs (Finset.mem_filter.mp hc).1)
        rw [hs, hms, sub_zero, add_zero]
        by_cases he : event rev v
        · simp [he, (hevent rev v he).1]
        · rw [if_neg he]; split_ifs <;> first | exact hP v | exact le_rfl
    have hall (D : Finset (List (ℕ × ℕ))) (hD : D ⊆ C) :
        (∑ v : Prefix k R, ∑ cs ∈ D, if cylinder rev cs v then P v else 0) =
          β rev * ∑ cs ∈ D, p ^ size cs := by
      rw [Finset.sum_comm, Finset.mul_sum]
      exact Finset.sum_congr rfl fun cs hc => hcylinder_mass rev cs (hD hc)
    have hh := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hpoint v)
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hall C (by intro cs hc; exact hc),
      hall (C.filter maximal) (Finset.filter_subset _ _)] at hh
    have hb := hboundary_mass rev
    nlinarith only [hh, hb]
  dsimp only
  constructor
  · simp only [Finset.sum_filter]
    have h := hbound false
    simp only [event, P, β, Bool.false_eq_true, if_false, Finset.sum_filter,
      p, π, size, maximal] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> rfl
  · simp only [Finset.sum_filter]
    have h := hbound true
    simp only [event, P, β, if_true, Finset.sum_filter, p, π, size, maximal] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> rfl

#print axioms parry_boundary_cylinder_bound

end D5.S3.TotalVariation.ParryBoundaryCylinderBound
