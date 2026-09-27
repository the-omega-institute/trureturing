/- GID: D5/S3/TotalVariation/ParryWordCollision
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParryWordCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Parry word masses telescope and overlapping collisions have exponential bounds. -/

import D5.S3.TotalVariation.ParryResetLaw
import D5.S3.TotalVariation.TwistedPrefixComparison

open scoped BigOperators
open D5.S3.TotalVariation.TwistedResetPaths
open D5.S3.TotalVariation.TwistedPrefixComparison
open D5.S3.TotalVariation.ParryResetLaw
namespace D5.S3.TotalVariation.ParryWordCollision

/-- Relation bits of a path, including its transition out of the initial state. -/
def relations {k n : ℕ} (s : State k) (v : Fin n → State k) (i : Fin n) : Bool :=
  let u : Fin (n + 1) → State k := Fin.cons s v
  !(xor (u i.castSucc).1 (v i).1)

/-- Every supported path telescopes to its endpoint ratio. For a specified relation
word there is at most one supported path from a fixed signed state, so its entire
conditional mass has the same uniform bound, including inadmissible words. -/
theorem parry_word_mass (k : ℕ) (hk : 2 ≤ k) :
    let p := parryParameter k
    (∀ (n : ℕ) (s : State k) (v : Fin n → State k),
      pathWeight k p n s v ≠ 0 →
      pathWeight k p n s v = p ^ n * suffixWeight k p (endpoint n s v).2 /
        suffixWeight k p s.2) ∧
    (∀ (m : ℕ), 1 ≤ m → ∀ (s : State k) (w : Fin m → Bool),
      (∑ v : Fin m → State k with relations s v = w, pathWeight k p m s v) ≤
        p ^ (m - 1)) := by
  classical
  let p := parryParameter k
  obtain ⟨hr, hb, _, hQ, _, _, _, _, _⟩ := parry_stationary_law k hk
  have hp : 0 < p := by dsimp [p]; linarith [hr.1]
  have hh (j : Fin k) : 0 < suffixWeight k p j := lt_of_lt_of_le hp (hb j).1
  have hzero : suffixWeight k p ⟨0, by omega⟩ = 1 := by
    simpa [suffixWeight, rootSum] using hr.2.2
  have hedge (s t : State k) (h : kernel k p s t ≠ 0) :
      kernel k p s t = p * suffixWeight k p t.2 / suffixWeight k p s.2 := by
    unfold kernel at h ⊢
    split_ifs with h0 h1
    · have ht : t.2 = ⟨0, by omega⟩ := Fin.ext h0.2
      rw [ht, hzero, mul_one]
    · rfl
    · simp [h0, h1] at h
  have htel : ∀ (n : ℕ) (s : State k) (v : Fin n → State k),
      pathWeight k p n s v ≠ 0 →
      pathWeight k p n s v = p ^ n * suffixWeight k p (endpoint n s v).2 /
        suffixWeight k p s.2 := by
    intro n
    induction n with
    | zero => intro s v _; simp [pathWeight, endpoint, (hh s.2).ne']
    | succ n ih =>
      intro s v hv
      have hn := mul_ne_zero_iff.mp hv
      rw [pathWeight, hedge s (v 0) hn.1, ih _ _ hn.2]
      simp only [endpoint, pow_succ]
      field_simp [(hh (v 0).2).ne', (hh s.2).ne']
  have hunique : ∀ (n : ℕ) (s : State k) (v u : Fin n → State k),
      pathWeight k p n s v ≠ 0 → pathWeight k p n s u ≠ 0 →
      relations s v = relations s u → v = u := by
    intro n
    induction n with
    | zero => intro s v u _ _ _; exact Subsingleton.elim _ _
    | succ n ih =>
      intro s v u hv hu he
      have hv' := mul_ne_zero_iff.mp hv
      have hu' := mul_ne_zero_iff.mp hu
      have hbit := congr_fun he 0
      simp only [relations, Fin.castSucc_zero, Fin.cons_zero] at hbit
      have hs : (v 0).1 = (u 0).1 := by
        cases h : s.1 <;> cases hvb : (v 0).1 <;> cases hub : (u 0).1 <;>
          simp_all only [Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.not_false,
            Bool.false_eq_true, Bool.true_eq_false]
      have hsupp (t : State k) (ht : kernel k p s t ≠ 0) :
          (t.1 = !s.1 ∧ t.2.val = 0) ∨
          (t.1 = s.1 ∧ t.2.val = s.2.val + 1) := by
        by_contra hn
        simp only [not_or] at hn
        simp [kernel, hn.1, hn.2] at ht
      have hv0 := hsupp (v 0) hv'.1
      have hu0 := hsupp (u 0) hu'.1
      have hstate : v 0 = u 0 := by
        apply Prod.ext hs
        apply Fin.ext
        rcases hv0 with hv0 | hv0 <;> rcases hu0 with hu0 | hu0
        · omega
        · have hbad : s.1 = !s.1 := hu0.1.symm.trans (hs.symm.trans hv0.1)
          cases s.1 <;> simp at hbad
        · have hbad : s.1 = !s.1 := hv0.1.symm.trans (hs.trans hu0.1)
          cases s.1 <;> simp at hbad
        · omega
      have htail : (fun i : Fin n => v i.succ) = (fun i : Fin n => u i.succ) := by
        apply ih (v 0) _ _ hv'.2
        · simpa [hstate] using hu'.2
        · funext i
          have he' := congr_fun he i.succ
          have hcv : (Fin.cons (v 0) (fun j : Fin n => v j.succ) :
              Fin (n+1) → State k) = v := Fin.cons_self_tail v
          have hcu : (Fin.cons (v 0) (fun j : Fin n => u j.succ) :
              Fin (n+1) → State k) = u := by rw [hstate]; exact Fin.cons_self_tail u
          simpa only [relations, ← Fin.succ_castSucc, Fin.cons_succ, hcv, hcu] using he'
      funext i
      refine Fin.cases hstate (fun j => congr_fun htail j) i
  refine ⟨htel, ?_⟩
  intro m hm s w
  by_cases hex : ∃ v : Fin m → State k,
      relations s v = w ∧ pathWeight k p m s v ≠ 0
  · obtain ⟨v, hv, hn⟩ := hex
    rw [Finset.sum_eq_single v]
    · rw [htel m s v hn]
      apply (div_le_iff₀ (hh s.2)).mpr
      have hpow : p ^ m = p ^ (m-1) * p := by
        rw [← pow_succ]; congr 1; omega
      rw [hpow]
      calc
        p ^ (m-1) * p * suffixWeight k p (endpoint m s v).2 ≤ p ^ (m-1) * p := by
          exact mul_le_of_le_one_right (by positivity) (hb _).2
        _ ≤ _ := mul_le_mul_of_nonneg_left (hb _).1 (pow_nonneg hp.le _)
    · intro u hu huv
      by_contra hun
      exact huv (hunique m s u v hun hn ((Finset.mem_filter.mp hu).2.trans hv.symm))
    · simp [hv]
  · have hz (v : Fin m → State k) (hv : relations s v = w) :
        pathWeight k p m s v = 0 := by
      by_contra hn
      exact hex ⟨v, hv, hn⟩
    rw [Finset.sum_eq_zero (fun v hv => hz v (Finset.mem_filter.mp hv).2)]
    exact pow_nonneg hp.le _


/-- Equality of two complete relation words inside one actual state path. -/
abbrev Collision {k n : ℕ} (m a b : ℕ) (ha : a + m ≤ n) (hb : b + m ≤ n)
    (s : State k) (v : Fin n → State k) : Prop :=
  ∀ i : Fin m, relations s v ⟨a+i.val, by omega⟩ =
    relations s v ⟨b+i.val, by omega⟩

/-- Distinct starts may overlap. Their equality still specifies only one future
relation word after the later start, and the actual stationary Parry mass is at
most the conditional word bound. No independence of the two occurrences is used. -/
theorem parry_overlapping_collision (k : ℕ) (hk : 2 ≤ k)
    (n m a b : ℕ) (hm : 1 ≤ m) (hab : a < b) (hb : b + m ≤ n) :
    (∑ v : Prefix k n with Collision m a b (by omega) hb v.1 v.2,
      referenceLaw k (parryParameter k) n (parryLaw k) v) ≤
      parryParameter k ^ (m - 1) := by
  classical
  let p := parryParameter k
  obtain ⟨hr, _, _, hQ, hrow, hπ, hπsum, _, _⟩ := parry_stationary_law k hk
  have hp : 0 < p := by dsimp [p]; linarith [hr.1]
  have hw : ∀ (l : ℕ) (s : State k) (v : Fin l → State k),
      0 ≤ pathWeight k p l s v := by
    intro l
    induction l with
    | zero => intro s v; exact zero_le_one
    | succ l ih => intro s v; exact mul_nonneg (hQ _ _) (ih _ _)
  have hrows : ∀ (l : ℕ) (s : State k),
      (∑ v : Fin l → State k, pathWeight k p l s v) = 1 := by
    intro l
    induction l with
    | zero => intro s; simp [pathWeight]
    | succ l ih =>
      intro s
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (l+1) => State k)]
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
      simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ,
        ]
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
  have hshort (s : State k) :
      (∑ v : Fin (b+m) → State k with Collision m a b (by omega) (by omega) s v,
        pathWeight k p (b+m) s v) ≤ p ^ (m-1) := by
    rw [Finset.sum_filter, ← Equiv.sum_comp (Fin.appendEquiv b m), Fintype.sum_prod_type]
    simp only [Fin.appendEquiv, Equiv.coe_fn_mk, happ]
    have hlocal (u : Fin b → State k) :
        (∑ v : Fin m → State k,
          if Collision m a b (by omega) (by omega) s (Fin.append u v) then
            pathWeight k p m (endpoint b s u) v else 0) ≤ p ^ (m-1) := by
      let E (v : Fin m → State k) := Collision m a b (by omega) (by omega) s (Fin.append u v)
      by_cases hex : ∃ v, E v
      · obtain ⟨v₀, hv₀⟩ := hex
        have hforced (v : Fin m → State k) (hv : E v) :
            relations (endpoint b s u) v = relations (endpoint b s u) v₀ := by
          have hbits : ∀ j : ℕ, (hj : j < m) →
              relations (endpoint b s u) v ⟨j,hj⟩ =
              relations (endpoint b s u) v₀ ⟨j,hj⟩ := by
            intro j
            induction j using Nat.strong_induction_on with
            | h j ih =>
              intro hj
              have he := hv ⟨j,hj⟩
              have he₀ := hv₀ ⟨j,hj⟩
              have hbidx : (⟨b+j, by omega⟩ : Fin (b+m)) = (⟨j,hj⟩ : Fin m).natAdd b := rfl
              rw [hbidx, hrpost] at he he₀
              rw [← he, ← he₀]
              by_cases haj : a+j < b
              · have hidx : (⟨a+j, by omega⟩ : Fin (b+m)) =
                    (⟨a+j,haj⟩ : Fin b).castAdd m := rfl
                rw [hidx, hrpre, hrpre]
              · have hj' : a+j-b < j := by omega
                have hidx : (⟨a+j, by omega⟩ : Fin (b+m)) =
                    (⟨a+j-b, by omega⟩ : Fin m).natAdd b := by apply Fin.ext; simp; omega
                rw [hidx, hrpost, hrpost]
                exact ih _ hj' (by omega)
          funext i
          exact hbits i.val i.isLt
        calc
          _ ≤ ∑ v : Fin m → State k,
              if relations (endpoint b s u) v = relations (endpoint b s u) v₀ then
                pathWeight k p m (endpoint b s u) v else 0 := by
            apply Finset.sum_le_sum
            intro v _
            by_cases hv : E v
            · change (if E v then _ else _) ≤ _
              rw [if_pos hv, if_pos (hforced v hv)]
            · simp only [show ¬ Collision m a b (by omega) (by omega) s (Fin.append u v) from hv,
                ↓reduceIte]
              split_ifs
              · exact hw _ _ _
              · exact le_rfl
          _ ≤ _ := by
            rw [← Finset.sum_filter]
            exact (parry_word_mass k hk).2 m hm _ _
      · have hn (v) : ¬ E v := fun h => hex ⟨v,h⟩
        simp only [show ∀ v, ¬ Collision m a b (by omega) (by omega) s (Fin.append u v) from hn,
          ↓reduceIte, Finset.sum_const_zero]
        exact pow_nonneg hp.le _
    calc
      _ = ∑ u : Fin b → State k, pathWeight k p b s u *
          ∑ v : Fin m → State k,
            if Collision m a b (by omega) (by omega) s (Fin.append u v) then
              pathWeight k p m (endpoint b s u) v else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        split_ifs <;> simp
      _ ≤ ∑ u : Fin b → State k, pathWeight k p b s u * p^(m-1) :=
        Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hlocal u) (hw _ _ _)
      _ = _ := by rw [← Finset.sum_mul, hrows, one_mul]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hb
  have hfull (s : State k) :
      (∑ v : Fin (b+m+t) → State k with Collision m a b (by omega) (by omega) s v,
        pathWeight k p (b+m+t) s v) ≤ p^(m-1) := by
    rw [Finset.sum_filter, ← Equiv.sum_comp (Fin.appendEquiv (b+m) t), Fintype.sum_prod_type]
    simp only [Fin.appendEquiv, Equiv.coe_fn_mk, happ]
    have hE (u : Fin (b+m) → State k) (v : Fin t → State k) :
        Collision m a b (by omega) (by omega) s (Fin.append u v) ↔
          Collision m a b (by omega) (by omega) s u := by
      unfold Collision
      have hidx (x : ℕ) (hx : x+m ≤ b+m) (i : Fin m) :
          (⟨x+i.val, by omega⟩ : Fin (b+m+t)) =
          (⟨x+i.val, by omega⟩ : Fin (b+m)).castAdd t := rfl
      simp only [hidx a (by omega), hidx b (by omega), hrpre]
    simp_rw [hE]
    calc
      _ = ∑ u : Fin (b+m) → State k,
          if Collision m a b (by omega) (by omega) s u then pathWeight k p (b+m) s u else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_ite_irrel]
        simp only [← Finset.mul_sum, hrows, mul_one, Finset.sum_const_zero]
      _ ≤ _ := by simpa only [Finset.sum_filter] using hshort s
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [referenceLaw]
  calc
    _ = ∑ s : State k, parryLaw k s *
        ∑ v : Fin (b+m+t) → State k with Collision m a b (by omega) (by omega) s v,
          pathWeight k p (b+m+t) s v := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> simp [p]
    _ ≤ ∑ s : State k, parryLaw k s * p^(m-1) :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hfull s) (hπ s)
    _ = _ := by rw [← Finset.sum_mul, hπsum, one_mul]

#print axioms parry_word_mass
#print axioms parry_overlapping_collision
end D5.S3.TotalVariation.ParryWordCollision
