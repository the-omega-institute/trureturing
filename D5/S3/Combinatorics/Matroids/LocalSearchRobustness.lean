/- GID: D5/S3/Combinatorics/Matroids/LocalSearchRobustness
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/LocalSearchRobustness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual base-neighborhood maxima control accumulated local-search errors. -/

import D5.S3.Combinatorics.Matroids.PrescribedExchange

/-! # Local-search robustness on native matroid bases -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Matroids.LocalSearchRobustness

open Set Matroid
open scoped BigOperators
open NativeWeightedBaseRankSaturation

universe u
variable {E : Type u} [Finite E]
noncomputable local instance : Fintype E := Fintype.ofFinite E
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

private theorem exists_neighborhood_max (M : Matroid E) (w : E → ℝ)
    (B : {B : Set E // M.IsBase B}) (t : ℕ) :
    ∃ A : Set E, (M.IsBase A ∧ (A \ B.val).ncard ≤ t) ∧
      ∀ D, M.IsBase D ∧ (D \ B.val).ncard ≤ t → baseWeight w D ≤ baseWeight w A := by
  classical
  apply Set.exists_max_image {D | M.IsBase D ∧ (D \ B.val).ncard ≤ t} (baseWeight w)
  · exact M.ground_finite.finite_subsets.subset (fun D hD => hD.1.subset_ground)
  · exact ⟨B.val, B.property, by simp⟩

/-- Maximum of the weight on the actual radius-t base neighborhood, attained by construction. -/
noncomputable def neighborhoodMax (M : Matroid E) (w : E → ℝ)
    (B : {B : Set E // M.IsBase B}) (t : ℕ) : ℝ :=
  baseWeight w (Classical.choose (exists_neighborhood_max M w B t))

private theorem max_spec (M : Matroid E) (w : E → ℝ)
    (B : {B : Set E // M.IsBase B}) (t : ℕ) :
    ∃ A : Set E, M.IsBase A ∧ (A \ B.val).ncard ≤ t ∧
      baseWeight w A = neighborhoodMax M w B t ∧
      ∀ D, M.IsBase D → (D \ B.val).ncard ≤ t → baseWeight w D ≤ neighborhoodMax M w B t := by
  obtain ⟨hA, hmax⟩ := Classical.choose_spec (exists_neighborhood_max M w B t)
  exact ⟨_, hA.1, hA.2, rfl, fun D hD hd => hmax D ⟨hD, hd⟩⟩

private theorem le_max (M : Matroid E) (w : E → ℝ)
    (B : {B : Set E // M.IsBase B}) (t : ℕ) {A : Set E}
    (hA : M.IsBase A) (hd : (A \ B.val).ncard ≤ t) :
    baseWeight w A ≤ neighborhoodMax M w B t := by
  obtain ⟨_, _, _, _, hmax⟩ := max_spec M w B t
  exact hmax A hA hd

private theorem weight_univ (w : E → ℝ) (A : Set E) :
    baseWeight w A = ∑ e : E, if e ∈ A then w e else 0 := by
  classical
  have h : A.toFinite.toFinset = Finset.univ.filter (fun e => e ∈ A) := by ext; simp
  simp only [baseWeight, h, Finset.sum_filter]

private theorem pair_weight (w : E → ℝ) {A B U V : Set E}
    (hU : U ⊆ A \ B) (hV : V ⊆ B \ A) :
    baseWeight w ((A \ U) ∪ V) + baseWeight w ((B \ V) ∪ U) =
      baseWeight w A + baseWeight w B := by
  classical
  simp only [weight_univ]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hu := @hU e
  have hv := @hV e
  by_cases heU : e ∈ U <;> by_cases heV : e ∈ V <;>
    by_cases heA : e ∈ A <;> by_cases heB : e ∈ B <;> simp_all

private theorem exchange_distance {A B U V : Set E}
    (hU : U ⊆ A \ B) (hV : V ⊆ B) :
    (((A \ U) ∪ V) \ B).ncard + U.ncard = (A \ B).ncard := by
  have heq : ((A \ U) ∪ V) \ B = (A \ B) \ U := by
    ext e; have hv := @hV e; simp only [mem_sdiff, mem_union]; tauto
  rw [heq]
  exact ncard_sdiff_add_ncard_of_subset hU

private theorem singleton_exchange (M : Matroid E) {A B : Set E}
    (hA : M.IsBase A) (hB : M.IsBase B) {a : E} (ha : a ∈ A \ B) :
    ∃ b ∈ B \ A, M.IsBase (insert b (A \ {a})) ∧
      M.IsBase (insert a (B \ {b})) := by
  classical
  obtain ⟨U,V,hU,hV,hx,_,hc,hcap,heA,heB⟩ :=
    PrescribedExchange.exists_prescribed_exchange M hA hB
      (X := {a}) (Y := ∅) (singleton_subset_iff.mpr ha) (empty_subset _)
  have hle : U.ncard ≤ 1 := by
    apply hcap.trans
    simpa using ENat.toNat_le_toNat (M.eRk_singleton_le a) (by simp)
  have hUa : a ∈ U := hx (mem_singleton a)
  have hUeq : U = {a} := by
    ext e
    exact ⟨fun he => ((ncard_le_one_iff (Set.toFinite U)).mp hle he hUa) ▸ mem_singleton a,
      fun he => (mem_singleton_iff.mp he).symm ▸ hUa⟩
  have hVcard : V.ncard = 1 := by simpa [hUeq] using hc.symm
  obtain ⟨b, hb⟩ := (ncard_eq_one.mp hVcard)
  refine ⟨b, hV (hb.symm ▸ mem_singleton b), ?_, ?_⟩
  · simpa [hUeq, hb, union_singleton] using heA
  · simpa [hUeq, hb, union_singleton] using heB

private theorem max_zero (M : Matroid E) (w : E → ℝ)
    (B : {B : Set E // M.IsBase B}) : neighborhoodMax M w B 0 = baseWeight w B.val := by
  obtain ⟨A,hA,hd,heq,_⟩ := max_spec M w B 0
  have hs : A ⊆ B.val := by
    apply sdiff_eq_empty.mp
    exact (ncard_eq_zero (Set.toFinite (A \ B.val))).mp (Nat.eq_zero_of_le_zero hd)
  have he : A = B.val := hA.eq_of_subset_isBase B.property hs
  simpa [he] using heq.symm


private theorem card_univ (S : Set E) :
    S.ncard = ∑ e : E, if e ∈ S then 1 else 0 := by
  classical
  have h : S.toFinite.toFinset = Finset.univ.filter (fun e => e ∈ S) := by ext; simp
  rw [ncard_eq_toFinset_card, h]
  simp

private theorem adjacent_distance {A B0 B1 : Set E} {x y : E}
    (h01 : B0 \ B1 = {x}) (h10 : B1 \ B0 = {y}) :
    (A \ B1).ncard + (if y ∈ A then 1 else 0) =
      (A \ B0).ncard + (if x ∈ A then 1 else 0) := by
  classical
  have hp (e : E) :
      (if e ∈ A \ B1 then 1 else 0) + (if e = y then (if y ∈ A then 1 else 0) else 0) =
      (if e ∈ A \ B0 then 1 else 0) + (if e = x then (if x ∈ A then 1 else 0) else 0) := by
    have h0 := Set.ext_iff.mp h01 e
    have h1 := Set.ext_iff.mp h10 e
    have hx : x ∈ B0 \ B1 := h01.symm ▸ mem_singleton x
    have hy : y ∈ B1 \ B0 := h10.symm ▸ mem_singleton y
    simp only [mem_sdiff, mem_singleton_iff] at h0 h1 hx hy
    by_cases heA : e ∈ A <;> by_cases he0 : e ∈ B0 <;> by_cases he1 : e ∈ B1 <;>
      by_cases hex : e = x <;> by_cases hey : e = y <;> simp_all
  have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun e _ => hp e)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hh
  simpa only [card_univ, mem_sdiff] using hh


/-- Oki–Schwarcz's joint-neighborhood comparison, with both maxima actually attained. -/
theorem neighborhood_comparison (M : Matroid E) (w : E → ℝ)
    (B0 B1 : {B : Set E // M.IsBase B}) (r : ℕ)
    (hstep : (B1.val \ B0.val).ncard ≤ 1) :
    neighborhoodMax M w B1 r + neighborhoodMax M w B0 1 ≥
      neighborhoodMax M w B0 (r + 1) + baseWeight w B1.val := by
  classical
  obtain ⟨A,hA,hd,hval,_⟩ := max_spec M w B0 (r + 1)
  rw [← hval]
  have finish {D F : Set E} (hD : M.IsBase D) (hDr : (D \ B1.val).ncard ≤ r)
      (hF : M.IsBase F) (hFr : (F \ B0.val).ncard ≤ 1)
      (hw : baseWeight w A + baseWeight w B1.val ≤ baseWeight w D + baseWeight w F) :
      baseWeight w A + baseWeight w B1.val ≤
        neighborhoodMax M w B1 r + neighborhoodMax M w B0 1 :=
    hw.trans (add_le_add (le_max M w B1 r hD hDr) (le_max M w B0 1 hF hFr))
  by_cases hnear : (A \ B1.val).ncard ≤ r
  · exact finish hA hnear B1.property hstep le_rfl
  by_cases heq : A = B0.val
  · subst A
    apply finish B1.property (by simp) B0.property (by simp)
    exact le_of_eq (add_comm _ _)
  by_cases h01eq : B0.val = B1.val
  · have hnon : (A \ B1.val).Nonempty := (ncard_pos (Set.toFinite _)).mp (by omega)
    obtain ⟨a,ha⟩ := hnon
    obtain ⟨b,hb,hD,hF⟩ := singleton_exchange M hA B1.property ha
    have hdist := exchange_distance (A := A) (B := B1.val) (U := {a}) (V := {b})
      (singleton_subset_iff.mpr ha) (singleton_subset_iff.mpr hb.1)
    have hDr : ((insert b (A \ {a})) \ B1.val).ncard ≤ r := by
      simp only [union_singleton, ncard_singleton] at hdist
      rw [h01eq] at hd
      omega
    have hFr : ((insert a (B1.val \ {b})) \ B0.val).ncard ≤ 1 := by
      apply (ncard_le_ncard (t := {a}) ?_).trans (by simp)
      rw [h01eq]
      intro e he
      simp only [mem_sdiff, mem_insert_iff] at he
      rcases he.1 with h | h
      · exact h
      · exact (he.2 h.1).elim
    apply finish hD hDr hF hFr
    exact le_of_eq (by simpa [union_singleton] using
      (pair_weight w (singleton_subset_iff.mpr ha) (singleton_subset_iff.mpr hb)).symm)
  obtain h10empty | ⟨y,h10⟩ := (ncard_le_one_iff_eq (Set.toFinite (B1.val \ B0.val))).mp hstep
  · exact (h01eq (B1.property.eq_of_subset_isBase B0.property
      (sdiff_eq_empty.mp h10empty)).symm).elim
  have h01card : (B0.val \ B1.val).ncard = 1 := by
    rw [B0.property.ncard_sdiff_comm B1.property, h10, ncard_singleton]
  obtain ⟨x,h01⟩ := ncard_eq_one.mp h01card
  have hx : x ∈ B0.val \ B1.val := h01.symm ▸ mem_singleton x
  have hy : y ∈ B1.val \ B0.val := h10.symm ▸ mem_singleton y
  have hdist := adjacent_distance (A := A) h01 h10
  have hB1 : B1.val = insert y (B0.val \ {x}) := by
    ext e
    have h0 := Set.ext_iff.mp h01 e
    have h1 := Set.ext_iff.mp h10 e
    simp only [mem_insert_iff, mem_sdiff, mem_singleton_iff] at *
    tauto
  by_cases hyA : y ∈ A
  · by_cases hxA : x ∈ A
    · obtain ⟨b,hb,hD,hF⟩ := singleton_exchange M hA B1.property ⟨hxA,hx.2⟩
      have hDr := exchange_distance (A := A) (B := B1.val) (U := {x}) (V := {b})
        (singleton_subset_iff.mpr ⟨hxA,hx.2⟩) (singleton_subset_iff.mpr hb.1)
      simp only [union_singleton, ncard_singleton] at hDr
      have hr : ((insert b (A \ {x})) \ B1.val).ncard ≤ r := by
        simp only [hyA,hxA,ite_true] at hdist; omega
      have hf : ((insert x (B1.val \ {b})) \ B0.val).ncard ≤ 1 := by
        apply (ncard_le_ncard (t := {y}) ?_).trans (by simp)
        intro e he
        simp only [mem_sdiff, mem_insert_iff] at he
        rcases he.1 with h | h
        · exact (he.2 (h ▸ hx.1)).elim
        · exact h10.subset ⟨h.1,he.2⟩
      apply finish hD hr hF hf
      exact le_of_eq (by simpa [union_singleton] using
        (pair_weight w (singleton_subset_iff.mpr ⟨hxA,hx.2⟩)
          (singleton_subset_iff.mpr hb)).symm)
    · simp only [hyA,hxA,ite_true,ite_false,add_zero] at hdist
      exact (hnear (by omega)).elim
  by_cases hxA : x ∈ A
  · have hnon : (A \ B0.val).Nonempty := by
      by_contra hn
      have hs : A ⊆ B0.val := sdiff_eq_empty.mp (not_nonempty_iff_eq_empty.mp hn)
      exact heq (hA.eq_of_subset_isBase B0.property hs)
    obtain ⟨U,V,hU,hV,hxU,hyV,hcard,hcap,hAU,hBV⟩ :=
      PrescribedExchange.exists_prescribed_exchange M hA B1.property
        (X := {x}) (Y := {y}) (singleton_subset_iff.mpr ⟨hxA,hx.2⟩)
        (singleton_subset_iff.mpr ⟨hy.1,hyA⟩)
    have hxU' : x ∈ U := hxU (mem_singleton x)
    have hyV' : y ∈ V := hyV (mem_singleton y)
    have htwo : U.ncard ≤ 2 := by
      apply hcap.trans
      have hrank := M.eRk_le_encard ({x} ∪ {y})
      have henc : ({x} ∪ {y} : Set E).encard ≤ 2 := by
        calc
          _ ≤ ({x} : Set E).encard + ({y} : Set E).encard := encard_union_le _ _
          _ = 2 := by simp; rfl
      simpa using ENat.toNat_le_toNat (hrank.trans henc) (by simp)
    have hone : 1 ≤ U.ncard := Nat.one_le_iff_ne_zero.mpr (ncard_ne_zero_of_mem hxU')
    by_cases hsize : U.ncard = 1
    · have hUeq : U = {x} := by
        ext e
        exact ⟨fun he => ((ncard_le_one_iff (Set.toFinite U)).mp (by omega) he hxU') ▸ mem_singleton x,
          fun he => (mem_singleton_iff.mp he).symm ▸ hxU'⟩
      have hVeq : V = {y} := by
        ext e
        exact ⟨fun he => ((ncard_le_one_iff (Set.toFinite V)).mp (by omega) he hyV') ▸ mem_singleton y,
          fun he => (mem_singleton_iff.mp he).symm ▸ hyV'⟩
      have hA' : M.IsBase (insert y (A \ {x})) := by
        simpa [hUeq,hVeq,union_singleton] using hAU
      obtain ⟨amin,hamin,hmin⟩ := Set.exists_min_image (A \ B0.val) w (Set.toFinite _) hnon
      have hamin' : amin ∈ (insert y (A \ {x})) \ B1.val := by
        have hxne : amin ≠ x := fun he => hamin.2 (he ▸ hx.1)
        have haminB : amin ∉ B1.val := by
          intro hh
          have hyEq := h10.subset ⟨hh,hamin.2⟩
          exact hyA (mem_singleton_iff.mp hyEq ▸ hamin.1)
        exact ⟨Or.inr ⟨hamin.1,by simpa using hxne⟩,haminB⟩
      obtain ⟨b,hb,hD⟩ := hA'.exchange B1.property hamin'
      have hb0 : b ∈ B0.val \ A := by
        have hbne : b ≠ y := fun he => hb.2 (Or.inl he)
        have hb0 : b ∈ B0.val := by
          by_contra hn
          exact hbne (mem_singleton_iff.mp (h10.subset ⟨hb.1,hn⟩))
        have hbnA : b ∉ A := by
          intro hh
          have hbneX : b ≠ x := fun he => hx.2 (he ▸ hb.1)
          exact hb.2 (Or.inr ⟨hh,by simpa using hbneX⟩)
        exact ⟨hb0,hbnA⟩
      obtain ⟨a,ha,hF⟩ := B0.property.exchange hA hb0
      have hDr0 := exchange_distance (A := A) (B := B1.val) (U := {x}) (V := {y})
        (singleton_subset_iff.mpr ⟨hxA,hx.2⟩) (singleton_subset_iff.mpr hy.1)
      have hDr1 := exchange_distance (A := insert y (A \ {x})) (B := B1.val)
        (U := {amin}) (V := {b}) (singleton_subset_iff.mpr hamin')
        (singleton_subset_iff.mpr hb.1)
      simp only [union_singleton,ncard_singleton] at hDr0 hDr1
      have hDr : ((insert b ((insert y (A \ {x})) \ {amin})) \ B1.val).ncard ≤ r := by
        simp only [hyA,hxA,ite_false,ite_true,add_zero] at hdist
        omega
      have hFr : ((insert a (B0.val \ {b})) \ B0.val).ncard ≤ 1 := by
        apply (ncard_le_ncard (t := {a}) ?_).trans (by simp)
        intro e he
        have hn := he.2
        simp only [mem_sdiff,mem_insert_iff] at he
        rcases he.1 with he | he
        · exact he
        · exact (hn he.1).elim
      apply finish hD hDr hF hFr
      rw [baseWeight_exchange w hb.2 hamin'.1, baseWeight_exchange w hyA hxA,
        baseWeight_exchange w ha.2 hb0.1, hB1, baseWeight_exchange w hy.2 hx.1]
      have hm := hmin a ha
      linarith
    · have hsize2 : U.ncard = 2 := by omega
      have hDr0 := exchange_distance hU (hV.trans sdiff_subset)
      have hDr : (((A \ U) ∪ V) \ B1.val).ncard ≤ r := by
        simp only [hyA,hxA,ite_false,ite_true,add_zero] at hdist
        omega
      have hfsub : (((B1.val \ V) ∪ U) \ B0.val) ⊆ U \ {x} := by
        intro e he
        have hxnot : x ∉ ((B1.val \ V) ∪ U) \ B0.val := fun hh => hh.2 hx.1
        have henx : e ≠ x := fun hh => hxnot (hh ▸ he)
        refine ⟨?_,by simpa using henx⟩
        rcases he.1 with heB | heU
        · have hey := mem_singleton_iff.mp (h10.subset ⟨heB.1,he.2⟩)
          exact (heB.2 (hey ▸ hyV')).elim
        · exact heU
      have hFr : (((B1.val \ V) ∪ U) \ B0.val).ncard ≤ 1 := by
        have hh := ncard_sdiff_singleton_add_one hxU'
        have hh' := ncard_le_ncard hfsub
        omega
      exact finish hAU hDr hBV hFr (le_of_eq (pair_weight w hU hV).symm)
  · obtain ⟨a,ha,hF,hD⟩ := singleton_exchange M B1.property hA ⟨hy.1,hyA⟩
    have hDr0 := exchange_distance (A := A) (B := B1.val) (U := {a}) (V := {y})
      (singleton_subset_iff.mpr ha) (singleton_subset_iff.mpr hy.1)
    simp only [union_singleton,ncard_singleton] at hDr0
    have hDr : ((insert y (A \ {a})) \ B1.val).ncard ≤ r := by
      simp only [hyA,hxA,ite_false,add_zero] at hdist
      omega
    have hFr : ((insert a (B1.val \ {y})) \ B0.val).ncard ≤ 1 := by
      apply (ncard_le_ncard (t := {a}) ?_).trans (by simp)
      intro e he
      have hn := he.2
      rcases he.1 with he | he
      · exact he
      · have hey := mem_singleton_iff.mp (h10.subset ⟨he.1,hn⟩)
        exact (he.2 (mem_singleton_iff.mpr hey)).elim
    apply finish hD hDr hF hFr
    exact le_of_eq (by simpa [union_singleton,add_comm] using
      (pair_weight w (singleton_subset_iff.mpr ⟨hy.1,hyA⟩)
        (singleton_subset_iff.mpr ha)).symm)


/-- The actual one-step neighborhood optimum minus the next base's weight. -/
noncomputable def localError (M : Matroid E) (w : E → ℝ)
    (B0 B1 : {B : Set E // M.IsBase B}) : ℝ :=
  neighborhoodMax M w B0 1 - baseWeight w B1.val

private theorem path_max_bound (M : Matroid E) (w : E → ℝ) (k : ℕ)
    (B : Fin (k + 1) → {B : Set E // M.IsBase B})
    (hstep : ∀ i : Fin k, ((B i.succ).val \ (B i.castSucc).val).ncard ≤ 1) :
    neighborhoodMax M w (B 0) k ≤ baseWeight w (B (Fin.last k)).val +
      ∑ i : Fin k, localError M w (B i.castSucc) (B i.succ) := by
  induction k with
  | zero => simpa using (max_zero M w (B 0)).le
  | succ k ih =>
    have hi := ih (fun i => B i.succ) (fun i => hstep i.succ)
    have hc := neighborhood_comparison M w (B 0) (B 1) k (hstep 0)
    simp only [Fin.sum_univ_succ]
    dsimp [localError] at *
    linarith

/-- Every local error is nonnegative and their sum controls every radius-k comparator. -/
theorem local_search_robustness (M : Matroid E) (w : E → ℝ) (k : ℕ)
    (B : Fin (k + 1) → {B : Set E // M.IsBase B})
    (hstep : ∀ i : Fin k, ((B i.succ).val \ (B i.castSucc).val).ncard ≤ 1) :
    (∀ i : Fin k, 0 ≤ localError M w (B i.castSucc) (B i.succ)) ∧
      ∀ C : Set E, M.IsBase C → (C \ (B 0).val).ncard ≤ k →
        baseWeight w C ≤ baseWeight w (B (Fin.last k)).val +
          ∑ i : Fin k, localError M w (B i.castSucc) (B i.succ) := by
  constructor
  · intro i
    exact sub_nonneg.mpr (le_max M w (B i.castSucc) 1 (B i.succ).property (hstep i))
  · intro C hC hdist
    exact (le_max M w (B 0) k hC hdist).trans (path_max_bound M w k B hstep)

#print axioms neighborhood_comparison
#print axioms local_search_robustness

end D5.S3.Combinatorics.Matroids.LocalSearchRobustness
