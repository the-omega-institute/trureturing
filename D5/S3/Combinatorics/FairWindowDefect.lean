/- GID: D5/S3/Combinatorics/FairWindowDefect
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FairWindowDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fair binary window rules have defect at least one over length plus two. -/

import D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FairWindowDefect

open scoped BigOperators
open D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments
open private prod_paritySign_cases from D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments

/-- The transport defect of a fixed table on one complete input context.
A zero relation bit reverses the output bit, and a one preserves it. -/
def defect {R : ℕ} (f : (Fin R → Fin 2) → Fin 2)
    (v : Fin (R + 1) → Fin 2) : ℚ :=
  if paritySign (f (fun i => v i.succ)) =
      paritySign (v (Fin.last R)) * paritySign (f (fun i => v i.castSucc))
  then 0 else 1

/-- Exact defect probability under independent fair relation bits: all complete
contexts have mass `2^(-(R+1))`. The table has no additional random input. -/
def fairDefect (R : ℕ) (f : (Fin R → Fin 2) → Fin 2) : ℚ :=
  (∑ v : Fin (R + 1) → Fin 2, defect f v) / 2 ^ (R + 1)

/-- The minimum over the finite nonempty set of deterministic window tables. -/
noncomputable def optimalFairDefect (R : ℕ) : ℚ :=
  Finset.univ.inf' ⟨(fun _ => 0), Finset.mem_univ _⟩ (fairDefect R)

/-- Every fixed deterministic window table, and therefore their exact finite
minimum, has defect at least `1/(R+2)` under the fair product input law. -/
theorem fair_window_defect_lower_bound (R : ℕ) :
    (∀ f : (Fin R → Fin 2) → Fin 2, 1 / (R + 2 : ℚ) ≤ fairDefect R f) ∧
      1 / (R + 2 : ℚ) ≤ optimalFairDefect R := by
  classical
  have hcompletion {L : ℕ} (_hL : 0 < L) (i : Fin L) (y : Fin L → Fin 2) :
      ∃! x : Fin L → Fin 2, (∀ j, j ≠ i → x j = y j) ∧ x ∈ parityFiber L (-1) := by
    let rest : ℤ := (Finset.univ.erase i).prod (fun j => paritySign (y j))
    have hrest : rest = -1 ∨ rest = 1 :=
      prod_paritySign_cases (Finset.univ.erase i) y
    have hprod (b : Fin 2) :
        (∏ j : Fin L, paritySign ((Function.update y i b) j)) =
          paritySign b * rest := by
      have hfun :
          (fun j : Fin L => paritySign ((Function.update y i b) j)) =
            Function.update (fun j : Fin L => paritySign (y j)) i (paritySign b) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]
      rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ i)]
      rw [Finset.sdiff_singleton_eq_erase]
    have hagree (b : Fin 2) : ∀ j, j ≠ i → (Function.update y i b) j = y j := by
      intro j hji
      simp [hji]
    have hodd0 : (Function.update y i 0) ∈ parityFiber L (-1) ↔ rest = 1 := by
      simp only [parityFiber, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hprod]
      simp [paritySign, rest]
    have hodd1 : (Function.update y i 1) ∈ parityFiber L (-1) ↔ rest = -1 := by
      simp only [parityFiber, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hprod]
      simp [paritySign, rest]
    rcases hrest with hrest | hrest
    · refine ⟨Function.update y i 1, ⟨hagree 1, hodd1.mpr hrest⟩, ?_⟩
      intro z hz
      have hz_update : z = Function.update y i (z i) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp
        · exact (hz.1 j hji).trans (by simp [hji])
      have hzi : z i = 0 ∨ z i = 1 := by omega
      rcases hzi with hzi | hzi
      · exfalso
        have hz_mem : z ∈ parityFiber L (-1) := hz.2
        rw [hz_update, hzi] at hz_mem
        have hzero := hodd0.mp hz_mem
        omega
      · calc
          z = Function.update y i (z i) := hz_update
          _ = Function.update y i 1 := by rw [hzi]
    · refine ⟨Function.update y i 0, ⟨hagree 0, hodd0.mpr hrest⟩, ?_⟩
      intro z hz
      have hz_update : z = Function.update y i (z i) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp
        · exact (hz.1 j hji).trans (by simp [hji])
      have hzi : z i = 0 ∨ z i = 1 := by omega
      rcases hzi with hzi | hzi
      · calc
          z = Function.update y i (z i) := hz_update
          _ = Function.update y i 0 := by rw [hzi]
      · exfalso
        have hz_mem : z ∈ parityFiber L (-1) := hz.2
        rw [hz_update, hzi] at hz_mem
        have hone := hodd1.mp hz_mem
        omega
  have hR : R < R + 2 := by omega
  let H := {x : Fin (R + 2) → Fin 2 // x ∈ parityFiber (R + 2) (-1)}
  let project (e : Equiv.Perm (Fin (R + 2))) (x : H) : Fin (R + 1) → Fin 2 :=
    fun i => x.val (e i.castSucc)
  have hproject (e : Equiv.Perm (Fin (R + 2))) : Function.Bijective (project e) := by
    constructor
    · intro x z hxz
      apply Subtype.ext
      have hagree : ∀ j, j ≠ e (Fin.last (R + 1)) → x.val j = z.val j := by
        intro j hj
        obtain ⟨k, rfl⟩ := e.surjective j
        induction k using Fin.lastCases with
        | last => exact (hj rfl).elim
        | cast i => exact congr_fun hxz i
      obtain ⟨w, hw, huniq⟩ := hcompletion
        (by omega : 0 < R + 2) (e (Fin.last (R + 1))) z.val
      exact (huniq x.val ⟨hagree, x.property⟩).trans
        (huniq z.val ⟨fun _ _ => rfl, z.property⟩).symm
    · intro v
      let y : Fin (R + 2) → Fin 2 := fun j => Fin.lastCases 0 v (e.symm j)
      obtain ⟨x, hx, _⟩ := hcompletion
        (by omega : 0 < R + 2) (e (Fin.last (R + 1))) y
      refine ⟨⟨x, hx.2⟩, ?_⟩
      funext i
      have hi : e i.castSucc ≠ e (Fin.last (R + 1)) := by
        exact fun h => Fin.castSucc_ne_last i (e.injective h)
      change x (e i.castSucc) = v i
      rw [hx.1 _ hi]
      simp [y]
  let rotate (e : Equiv.Perm (Fin (R + 2))) (x : H) : H :=
    ⟨fun j => x.val (e j), by
      simp only [parityFiber, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Equiv.prod_comp e (fun j => paritySign (x.val j))]
      simpa [parityFiber] using x.property⟩
  have hrotinv (e : Equiv.Perm (Fin (R + 2))) (x : H) :
      rotate e.symm (rotate e x) = x := by
    apply Subtype.ext
    funext j
    exact congrArg x.val (e.apply_symm_apply j)
  have hrotbij (e : Equiv.Perm (Fin (R + 2))) : Function.Bijective (rotate e) := by
    constructor
    · intro x y h
      have hi := congrArg (rotate e.symm) h
      simpa only [hrotinv] using hi
    · intro x
      refine ⟨rotate e.symm x, ?_⟩
      apply Subtype.ext
      funext j
      exact congrArg x.val (e.symm_apply_apply j)
  have hlaw (e : Equiv.Perm (Fin (R + 2))) (g : (Fin (R + 1) → Fin 2) → ℚ) :
      (∑ x : H, g (project e x)) = ∑ v, g v := by
    calc
      _ = ∑ x : H, g (project (Equiv.refl _) (rotate e x)) := rfl
      _ = ∑ x : H, g (project (Equiv.refl _) x) :=
        (hrotbij e).sum_comp (fun x => g (project (Equiv.refl _) x))
      _ = ∑ v, g v := (hproject (Equiv.refl _)).sum_comp g
  have hcard : (Fintype.card H : ℚ) = 2 ^ (R + 1) := by
    have hc := (parity_conditioned_moments (R + 1) (-1) (Or.inl rfl)).1
    have hcH : Fintype.card H = 2 ^ (R + 1) := by
      rw [Fintype.card_coe]
      exact hc
    exact_mod_cast hcH
  have hbound (f : (Fin R → Fin 2) → Fin 2) :
      1 / (R + 2 : ℚ) ≤ fairDefect R f := by
    let context (x : H) (u : Fin (R + 2)) : Fin (R + 1) → Fin 2 :=
      project (Equiv.addLeft u) x
    let output (x : H) (u : Fin (R + 2)) : Fin 2 :=
      f (fun i => x.val (u + i.castSucc.castSucc))
    have hcontext (x : H) (u : Fin (R + 2)) :
        defect f (context x u) =
          if paritySign (output x (u + 1)) =
              paritySign (x.val (u + (⟨R, hR⟩ : Fin (R + 2)))) * paritySign (output x u)
          then 0 else 1 := by
      have hsucc (i : Fin R) : i.succ.castSucc = (1 : Fin (R + 2)) + i.castSucc.castSucc := by
        apply Fin.ext
        simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 + i.val < R + 2 by omega)]
        omega
      have hlast : (Fin.last R).castSucc = (⟨R, hR⟩ : Fin (R + 2)) := rfl
      have hw : (fun i : Fin R => x.val (u + i.succ.castSucc)) =
          (fun i : Fin R => x.val (u + 1 + i.castSucc.castSucc)) := by
        funext i
        rw [hsucc]
        exact congrArg x.val (add_assoc u 1 i.castSucc.castSucc).symm
      change (if paritySign (f (fun i => x.val (u + i.succ.castSucc))) =
          paritySign (x.val (u + (Fin.last R).castSucc)) *
            paritySign (f (fun i => x.val (u + i.castSucc.castSucc)))
          then 0 else 1) = _
      rw [hw, hlast]
    have hcycle (x : H) : 1 ≤ ∑ u : Fin (R + 2), defect f (context x u) := by
      have hex : ∃ u : Fin (R + 2),
          paritySign (output x (u + 1)) ≠
            paritySign (x.val (u + (⟨R, hR⟩ : Fin (R + 2)))) * paritySign (output x u) := by
        by_contra h
        push Not at h
        have heq := congrArg (fun a : Fin (R + 2) → ℤ => ∏ u, a u) (funext h)
        have hshift := Equiv.prod_comp (Equiv.addRight (1 : Fin (R + 2)))
          (fun u => paritySign (output x u))
        have hrel := Equiv.prod_comp (Equiv.addRight (⟨R, hR⟩ : Fin (R + 2)))
          (fun u => paritySign (x.val u))
        change (∏ u, paritySign (output x (u + 1))) =
          ∏ u, paritySign (output x u) at hshift
        change (∏ u, paritySign (x.val (u + (⟨R, hR⟩ : Fin (R + 2))))) =
          ∏ u, paritySign (x.val u) at hrel
        have hodd : (∏ u, paritySign (x.val u)) = -1 := by
          simpa [parityFiber] using x.property
        have hnonzero : (∏ u, paritySign (output x u)) ≠ 0 := by
          apply Finset.prod_ne_zero_iff.mpr
          intro u _
          simp only [paritySign]
          split_ifs <;> norm_num
        simp only [Finset.prod_mul_distrib] at heq
        rw [hshift, hrel, hodd] at heq
        exact hnonzero (by linarith only [heq])
      obtain ⟨u, hu⟩ := hex
      have he : defect f (context x u) = 1 := by rw [hcontext, if_neg hu]
      calc
        1 = defect f (context x u) := he.symm
        _ ≤ ∑ i : Fin (R + 2), defect f (context x i) := by
          apply Finset.single_le_sum (s := Finset.univ)
            (f := fun i : Fin (R + 2) => defect f (context x i))
          · intro i _
            simp only [defect]
            split_ifs <;> norm_num
          · exact Finset.mem_univ _
    have hsum : (2 : ℚ) ^ (R + 1) ≤
        (R + 2 : ℚ) * ∑ v : Fin (R + 1) → Fin 2, defect f v := by
      calc
        (2 : ℚ) ^ (R + 1) = ∑ _x : H, (1 : ℚ) := by simp [hcard]
        _ ≤ ∑ x : H, ∑ u : Fin (R + 2), defect f (context x u) :=
          Finset.sum_le_sum (fun x _ => hcycle x)
        _ = ∑ u : Fin (R + 2), ∑ x : H, defect f (context x u) := Finset.sum_comm
        _ = ∑ _u : Fin (R + 2), ∑ v : Fin (R + 1) → Fin 2, defect f v := by
          apply Finset.sum_congr rfl
          intro u _
          exact hlaw (Equiv.addLeft u) (defect f)
        _ = (R + 2 : ℚ) * ∑ v : Fin (R + 1) → Fin 2, defect f v := by simp
    have hpos : (0 : ℚ) < R + 2 := by positivity
    have hpow : (0 : ℚ) < 2 ^ (R + 1) := by positivity
    rw [fairDefect, div_le_div_iff₀ hpos hpow]
    simpa [mul_comm] using hsum
  refine ⟨hbound, ?_⟩
  exact Finset.le_inf' _ _ (fun f _ => hbound f)

#print axioms fair_window_defect_lower_bound

end D5.S3.Combinatorics.FairWindowDefect
