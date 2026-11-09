/- GID: D5/S3/Combinatorics/Matroids/IntegralWeightSplitting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/IntegralWeightSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native finite matroids with a common base admit an integral optimal weight splitting. -/

import D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation
import D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierDual
import D5.S3.Combinatorics.Matroids.FiniteIntersectionPolytope
import Mathlib.Analysis.Convex.KreinMilman

/-! # Integral base optimality and weight splitting -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Matroids.IntegralWeightSplitting

open scoped BigOperators
open Set Matroid

universe u
variable {E : Type u} [Finite E]

/-- The actual integral finite sum over a set of carrier elements. -/
noncomputable def weightSum (q : E → ℤ) (B : Set E) : ℤ :=
  ∑ e ∈ B.toFinite.toFinset, q e

/-- Single-element exchange optimality implies optimality against every native base. -/
theorem exchange_local_is_global_minimum (M : Matroid E) (q : E → ℤ)
    {B : Set E} (hB : M.IsBase B)
    (hlocal : ∀ b ∈ B, ∀ e ∈ M.E \ B,
      M.IsBase (insert e (B \ {b})) → q b ≤ q e) :
    ∀ C, M.IsBase C → weightSum q B ≤ weightSum q C := by
  classical
  let r : E → ℝ := fun e => (q e : ℝ)
  have hsat : ∀ t : ℝ,
      (B ∩ NativeWeightedBaseRankSaturation.lowerWeightSet M r t).ncard =
        (M.eRk (NativeWeightedBaseRankSaturation.lowerWeightSet M r t)).toNat := by
    intro t
    let X := NativeWeightedBaseRankSaturation.lowerWeightSet M r t
    have hXE : X ⊆ M.E := fun _ h => h.1
    have hI : M.Indep (B ∩ X) := hB.indep.inter_right X
    have hBasis : M.IsBasis (B ∩ X) X := by
      by_contra hnot
      obtain ⟨J, hJ⟩ := M.exists_isBasis X hXE
      obtain ⟨e, heJ, heI⟩ :=
        hI.exists_insert_of_not_isBasis inter_subset_right hnot hJ
      have heX : e ∈ X := hJ.subset heJ.1
      have heNotB : e ∉ B := fun heB => heJ.2 ⟨heB, heX⟩
      obtain ⟨b, hb, hex⟩ :=
        D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.exchange_base_over_independent_subset
          hB heNotB heI
      have hbe : r b ≤ r e := by
        dsimp [r]
        exact_mod_cast hlocal b hb.1 e ⟨heX.1, heNotB⟩ hex
      have hbX : b ∈ X := ⟨hB.subset_ground hb.1, hbe.trans heX.2⟩
      exact hb.2 ⟨hb.1, hbX⟩
    rw [ncard_def, hBasis.encard_eq_eRk]
  have hmin := ((NativeWeightedBaseRankSaturation.native_weighted_base_rank_saturation
    M r).2 B hB).mpr hsat
  intro C hC
  have h := hmin C hC
  dsimp [NativeWeightedBaseRankSaturation.baseWeight, r] at h
  unfold weightSum
  exact_mod_cast h

#print axioms exchange_local_is_global_minimum

/-- Tagged native exchanges; `true` tags the first matroid. -/
def ExchangeArc (M₁ M₂ : Matroid E) (B : Set E) :=
  {a : Bool × E × E // a.2.1 ∈ B ∧ a.2.2 ∈ M₁.E \ B ∧
    (if a.1 = true then M₁ else M₂).IsBase (insert a.2.2 (B \ {a.2.1}))}

/-- The first matroid is oriented inside-to-outside and the second in reverse. -/
def exchangeGraph (M₁ M₂ : Matroid E) (B : Set E) :
    Maths.EdgeGraph E (ExchangeArc M₁ M₂ B) where
  source a := if a.val.1 = true then a.val.2.1 else a.val.2.2
  target a := if a.val.1 = true then a.val.2.2 else a.val.2.1

/-- The asymmetric integral arc weight in the closed-walk obstruction. -/
def exchangeWeight (M₁ M₂ : Matroid E) (B : Set E) (w : E → ℤ)
    (a : ExchangeArc M₁ M₂ B) : ℤ :=
  if a.val.1 = true then 0 else w a.val.2.1 - w a.val.2.2

private noncomputable def point (S : Set E) (e : E) : ℝ := by
  classical
  exact if e ∈ S then 1 else 0

omit [Finite E] in
private lemma point_nonneg (S : Set E) (e : E) : 0 ≤ point S e := by
  classical
  dsimp [point]
  split <;> norm_num

private noncomputable def linearTotal [Fintype E] (q : E → ℝ) : (E → ℝ) →L[ℝ] ℝ :=
  ∑ e, q e • ContinuousLinearMap.proj e

private lemma linearTotal_apply [Fintype E] (q x : E → ℝ) :
    linearTotal q x = ∑ e, q e * x e := by
  simp [linearTotal]

private lemma point_sum (S U : Set E) :
    (∑ e ∈ U.toFinite.toFinset, point S e) = ((S ∩ U).ncard : ℝ) := by
  classical
  rw [Set.ncard_eq_toFinset_card (S ∩ U)]
  have hf : U.toFinite.toFinset.filter (fun e => e ∈ S) =
      (S ∩ U).toFinite.toFinset := by
    ext e
    simp [and_comm]
  simp only [point, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hf]

private lemma point_feasible (M : Matroid E) {S : Set E} (hS : M.IsBase S) (U : Set E) :
    (∑ e ∈ U.toFinite.toFinset, point S e) ≤ ((M.eRk U).toNat : ℝ) := by
  rw [point_sum]
  have hi : M.Indep (S ∩ U) := hS.indep.inter_right U
  have hr : (S ∩ U).ncard ≤ (M.eRk U).toNat := by
    rw [ncard_def, ← hi.eRk_eq_encard]
    exact ENat.toNat_le_toNat (M.eRk_mono inter_subset_right)
      (M.isRkFinite_set U).eRk_lt_top.ne
  exact_mod_cast hr

private lemma point_total [Fintype E] (q : E → ℝ) (S : Set E) :
    linearTotal q (point S) = ∑ e ∈ S.toFinite.toFinset, q e := by
  classical
  rw [linearTotal_apply]
  simp only [point, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext e
  simp

omit [Finite E] in
private lemma point_exchange {B : Set E} {b e : E} (hb : b ∈ B) (he : e ∉ B)
    (x : E) :
    point (insert e (B \ {b})) x = point B x + point {e} x - point {b} x := by
  classical
  by_cases hxb : x = b
  · subst x
    have hbe : b ≠ e := fun h => he (h ▸ hb)
    simp [point, hb, hbe]
  · by_cases hxe : x = e
    · subst x
      have heb : e ≠ b := fun h => he (h ▸ hb)
      simp [point, he, heb]
    · by_cases hx : x ∈ B <;> simp [point, hx, hxb, hxe]

private noncomputable def arcPoint (M₁ M₂ : Matroid E) (B : Set E) (tag : Bool)
    (a : ExchangeArc M₁ M₂ B) : E → ℝ :=
  if a.val.1 = tag then point (insert a.val.2.2 (B \ {a.val.2.1})) else point B

private lemma walk_balance (M₁ M₂ : Matroid E) (B : Set E) {s t : E}
    (p : (exchangeGraph M₁ M₂ B).Walk s t) (x : E) :
    (p.edges.map (fun a => arcPoint M₁ M₂ B true a x)).sum -
      (p.edges.map (fun a => arcPoint M₁ M₂ B false a x)).sum =
        point {t} x - point {s} x := by
  induction p with
  | nil => simp
  | @concat t p a legal ih =>
    have hex := point_exchange a.property.1 a.property.2.1.2 x
    simp only [Maths.EdgeGraph.Walk.edges_concat, List.map_append, List.map_singleton,
      List.sum_append, List.sum_singleton]
    cases ht : a.val.1
    · have hs : a.val.2.2 = t := by simpa [exchangeGraph, ht] using legal
      have htarget : (exchangeGraph M₁ M₂ B).target a = a.val.2.1 := by simp [exchangeGraph, ht]
      rw [htarget]
      simp only [arcPoint, ht, Bool.false_eq_true, ite_false, ite_true]
      simp only [arcPoint, apply_ite] at ih ⊢
      have hsP : point {t} x = point {a.val.2.2} x := congrArg (fun e => point {e} x) hs.symm
      linear_combination ih - hex + hsP
    · have hs : a.val.2.1 = t := by simpa [exchangeGraph, ht] using legal
      have htarget : (exchangeGraph M₁ M₂ B).target a = a.val.2.2 := by simp [exchangeGraph, ht]
      rw [htarget]
      simp only [arcPoint, ht, Bool.true_eq_false, ite_false, ite_true]
      simp only [arcPoint, apply_ite] at ih ⊢
      have hsP : point {t} x = point {a.val.2.1} x := congrArg (fun e => point {e} x) hs.symm
      linear_combination ih + hex + hsP

private lemma sum_list_swap {A : Type*} (l : List A) (f : A → E → ℝ) (U : Finset E) :
    (∑ e ∈ U, (l.map (fun a => f a e)).sum) =
      (l.map (fun a => ∑ e ∈ U, f a e)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

private lemma list_bound {A : Type*} (l : List A) (f : A → ℝ) (r : ℝ)
    (hf : ∀ a ∈ l, f a ≤ r) : (l.map f).sum ≤ l.length * r := by
  have h := List.sum_le_length_nsmul (l.map f) r (by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact hf a ha)
  simpa only [List.length_map, nsmul_eq_mul] using h

/-- An optimal common base has no positive closed walk in the tagged exchange graph. -/
theorem optimal_common_base_closedWalk_nonpos (M₁ M₂ : Matroid E)
    (_hE : M₁.E = M₂.E) (w : E → ℤ) {B : Set E}
    (hB₁ : M₁.IsBase B) (hB₂ : M₂.IsBase B)
    (hmin : ∀ C, M₁.IsBase C → M₂.IsBase C → weightSum w B ≤ weightSum w C) :
    ∀ (s : E) (p : (exchangeGraph M₁ M₂ B).Walk s s),
      Maths.MaxPlusPotential.walkWeight (exchangeWeight M₁ M₂ B w) p ≤ 0 := by
  classical
  letI := Fintype.ofFinite E
  let P : Set (E → ℝ) := {x | (∀ e, 0 ≤ x e) ∧
    ∀ U : Set E, (∑ e ∈ U.toFinite.toFinset, x e) ≤ ((M₁.eRk U).toNat : ℝ) ∧
      (∑ e ∈ U.toFinite.toFinset, x e) ≤ ((M₂.eRk U).toNat : ℝ)}
  let card : (E → ℝ) →L[ℝ] ℝ := linearTotal (fun _ => 1)
  let cost : (E → ℝ) →L[ℝ] ℝ := linearTotal (fun e => (w e : ℝ))
  have hPB : point B ∈ P := ⟨fun e => by dsimp [point]; split <;> norm_num,
    fun U => ⟨point_feasible M₁ hB₁ U, point_feasible M₂ hB₂ U⟩⟩
  have hcard (S : Set E) : card (point S) = (S.ncard : ℝ) := by
    change linearTotal (fun _ => 1) (point S) = _
    rw [linearTotal_apply]
    simpa only [one_mul, Set.toFinite_toFinset, Set.toFinset_univ, Set.inter_univ] using point_sum S univ
  have hrank : (M₁.eRk univ).toNat = B.ncard := by
    rw [M₁.eRk_univ_eq, ← hB₁.encard_eq_eRank, ← ncard_def]
  have hcardle (x : E → ℝ) (hx : x ∈ P) : card x ≤ (B.ncard : ℝ) := by
    have h := (hx.2 univ).1
    rw [hrank] at h
    simpa [card, linearTotal_apply] using h
  have hclosed : IsClosed P := by
    dsimp [P]
    simp only [ofPred_and, ofPred_forall]
    exact (isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e)).inter
      (isClosed_iInter fun U => (isClosed_le (by fun_prop) continuous_const).inter
        (isClosed_le (by fun_prop) continuous_const))
  have hcompact : IsCompact P := by
    apply (isCompact_Icc : IsCompact (Icc (0 : E → ℝ) 1)).of_isClosed_subset hclosed
    intro x hx
    refine ⟨hx.1, fun e => ?_⟩
    change x e ≤ 1
    have h := (hx.2 {e}).1
    simp only [Set.toFinite_toFinset, Set.toFinset_singleton, Finset.sum_singleton] at h
    have hr : (M₁.eRk {e}).toNat ≤ 1 := by
      rw [← ENat.natCast_le_natCast, FiniteIntersection.cast_toNat_eRk]
      exact M₁.eRk_singleton_le e
    exact h.trans (by exact_mod_cast hr)
  let F := card.toExposed P
  have hF : IsExposed ℝ P F := ContinuousLinearMap.toExposed.isExposed
  have hFB : point B ∈ F := ⟨hPB, fun x hx => by rw [hcard]; exact hcardle x hx⟩
  have hround (z : E → ℝ) (hz : z ∈ P) (hzc : card z = (B.ncard : ℝ)) :
      ∃ C, M₁.IsBase C ∧ M₂.IsBase C ∧ cost (point C) ≤ cost z := by
    have hzF : z ∈ F := ⟨hz, fun x hx => by rw [hzc]; exact hcardle x hx⟩
    let A := (-cost).toExposed F
    have hA : IsExposed ℝ F A := ContinuousLinearMap.toExposed.isExposed
    obtain ⟨v, hvF, hvmin⟩ := (hF.isCompact hcompact).exists_isMinOn ⟨_, hzF⟩
      cost.continuous.continuousOn
    have hvA : v ∈ A := ⟨hvF, fun x hx => by
      simpa only [ContinuousLinearMap.neg_apply] using
        neg_le_neg (show cost v ≤ cost x from hvmin hx)⟩
    obtain ⟨v, hv⟩ := (hA.isCompact (hF.isCompact hcompact)).extremePoints_nonempty ⟨v, hvA⟩
    have hvP := (hF.isExtreme.trans hA.isExtreme).extremePoints_subset_extremePoints hv
    have hv01 : ∀ e, v e = 0 ∨ v e = 1 := by
      apply FiniteIntersectionPolytope.extreme_point_zero_one (M₁ ↾ univ) (M₂ ↾ univ) rfl rfl v
      simpa only [Matroid.restrict_eRk_eq' , Set.inter_univ] using hvP
    let C : Set E := {e | v e = 1}
    have hvpoint : v = point C := by
      funext e
      rcases hv01 e with he | he <;> simp [point, C, he]
    have hvc : card v = (B.ncard : ℝ) := le_antisymm (hcardle v hvP.1)
      (by simpa [hcard] using hv.1.1.2 (point B) hPB)
    have hCB : C.ncard = B.ncard := by
      rw [hvpoint, hcard] at hvc
      exact_mod_cast hvc
    have hbase (M : Matroid E) (hBM : M.IsBase B)
        (hbound : ∀ U : Set E, (∑ e ∈ U.toFinite.toFinset, v e) ≤ ((M.eRk U).toNat : ℝ)) :
        M.IsBase C := by
      have h := hbound C
      rw [hvpoint, point_sum, inter_self] at h
      have hc : C.ncard ≤ (M.eRk C).toNat := by exact_mod_cast h
      have henc : C.encard ≤ M.eRk C := by
        rw [← FiniteIntersection.cast_toNat_eRk M C, ← C.toFinite.cast_ncard_eq]
        exact_mod_cast hc
      have hi := (M.isRkFinite_set C).indep_of_encard_le_eRk henc
      apply hi.isBase_of_eRk_ge (Set.toFinite C)
      rw [hi.eRk_eq_encard, ← hBM.encard_eq_eRank,
        ← C.toFinite.cast_ncard_eq, ← B.toFinite.cast_ncard_eq, hCB]
    refine ⟨C, hbase M₁ hB₁ (fun U => (hvP.1.2 U).1),
      hbase M₂ hB₂ (fun U => (hvP.1.2 U).2), ?_⟩
    have h := hv.1.2 z hzF
    simpa [hvpoint] using neg_le_neg h
  intro s p
  let W : ℤ := Maths.MaxPlusPotential.walkWeight (exchangeWeight M₁ M₂ B w) p
  let k : ℝ := p.edges.length + 1
  have hk : 0 < k := by dsimp [k]; positivity
  let z (tag : Bool) (x : E) : ℝ :=
    (point B x + (p.edges.map (fun a => arcPoint M₁ M₂ B tag a x)).sum) / k
  have hzeq : z true = z false := by
    funext x
    have h := walk_balance M₁ M₂ B p x
    dsimp [z]
    congr 1
    linarith
  have harc (tag : Bool) (a : ExchangeArc M₁ M₂ B) :
      (if tag = true then M₁ else M₂).IsBase
        (if a.val.1 = tag then insert a.val.2.2 (B \ {a.val.2.1}) else B) := by
    by_cases ha : a.val.1 = tag
    · rw [if_pos ha]
      simpa only [ha] using a.property.2.2
    · rw [if_neg ha]
      cases tag <;> simp_all
  have hnonneg (tag : Bool) (x : E) : 0 ≤ z tag x := by
    apply div_nonneg _ hk.le
    apply add_nonneg (point_nonneg B x)
    apply List.sum_nonneg
    intro r hr
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hr
    simp only [arcPoint]
    split <;> exact point_nonneg _ x
  have hboundz (tag : Bool) (U : Set E) :
      (∑ e ∈ U.toFinite.toFinset, z tag e) ≤
        (((if tag = true then M₁ else M₂).eRk U).toNat : ℝ) := by
    let M := if tag = true then M₁ else M₂
    have hBM : M.IsBase B := by
      cases tag
      · exact hB₂
      · exact hB₁
    have hba : ∀ a ∈ p.edges,
        (∑ e ∈ U.toFinite.toFinset, arcPoint M₁ M₂ B tag a e) ≤ ((M.eRk U).toNat : ℝ) := by
      intro a _
      have h := point_feasible _ (harc tag a) U
      by_cases ha : a.val.1 = tag <;> simpa only [arcPoint, ha, ite_true, ite_false] using h
    have hb := point_feasible M hBM U
    have hl := list_bound p.edges
      (fun a => ∑ e ∈ U.toFinite.toFinset, arcPoint M₁ M₂ B tag a e)
      ((M.eRk U).toNat : ℝ) hba
    dsimp [z]
    rw [← Finset.sum_div, Finset.sum_add_distrib, sum_list_swap]
    apply (div_le_iff₀ hk).mpr
    dsimp [k]
    nlinarith
  have hzP : z true ∈ P := ⟨hnonneg true, fun U => ⟨hboundz true U,
    by rw [hzeq]; exact hboundz false U⟩⟩
  have hztotal (tag : Bool) : card (z tag) = (B.ncard : ℝ) := by
    have hca (a : ExchangeArc M₁ M₂ B) :
        (∑ e, arcPoint M₁ M₂ B tag a e) = (B.ncard : ℝ) := by
      have hBM : (if tag = true then M₁ else M₂).IsBase B := by
        cases tag
        · exact hB₂
        · exact hB₁
      have h := (harc tag a).ncard_eq_ncard_of_isBase hBM
      have hsum := point_sum
        (if a.val.1 = tag then insert a.val.2.2 (B \ {a.val.2.1}) else B) univ
      rw [Set.inter_univ] at hsum
      by_cases ha : a.val.1 = tag <;>
        simpa only [Set.toFinite_toFinset, Set.toFinset_univ, Set.inter_univ,
          arcPoint, ha, ite_true, ite_false] using hsum.trans (congrArg (fun n : ℕ => (n : ℝ)) h)
    have hb : (∑ e, point B e) = (B.ncard : ℝ) := by
      simpa only [Set.toFinite_toFinset, Set.toFinset_univ, Set.inter_univ] using point_sum B univ
    simp only [card, linearTotal_apply, one_mul, z]
    rw [← Finset.sum_div, Finset.sum_add_distrib, sum_list_swap, hb]
    have hmap : (p.edges.map (fun a => ∑ e, arcPoint M₁ M₂ B tag a e)).sum =
        p.edges.length * (B.ncard : ℝ) := by simp [hca]
    rw [hmap]
    apply (div_eq_iff hk.ne').mpr
    dsimp [k]
    ring
  obtain ⟨C, hC₁, hC₂, hCcost⟩ := hround (z true) hzP (hztotal true)
  have hminR : cost (point B) ≤ cost (point C) := by
    have h := hmin C hC₁ hC₂
    dsimp [weightSum] at h
    simpa only [cost, point_total, ← Int.cast_sum] using (Int.cast_le.mpr h :
      ((∑ e ∈ B.toFinite.toFinset, w e : ℤ) : ℝ) ≤
        ((∑ e ∈ C.toFinite.toFinset, w e : ℤ) : ℝ))
  have hcost : cost (point B) ≤ cost (z false) := by rw [← hzeq]; exact hminR.trans hCcost
  have hdrop (a : ExchangeArc M₁ M₂ B) :
      cost (arcPoint M₁ M₂ B false a) = cost (point B) - (exchangeWeight M₁ M₂ B w a : ℝ) := by
    by_cases ha : a.val.1 = true
    · simp [arcPoint, exchangeWeight, ha]
    · have ha' : a.val.1 = false := Bool.eq_false_iff.mpr ha
      simp only [arcPoint, ha', ite_true, exchangeWeight, Bool.false_eq_true, ite_false]
      have hp : point (insert a.val.2.2 (B \ {a.val.2.1})) =
          point B + point {a.val.2.2} - point {a.val.2.1} := by
        funext x
        exact point_exchange a.property.1 a.property.2.1.2 x
      rw [hp, map_sub, map_add]
      simp [cost, point_total]
      ring
  have hcavg : cost (z false) =
      cost (point B) - (W : ℝ) / k := by
    have hswap : (∑ e, (w e : ℝ) * (p.edges.map (fun a => arcPoint M₁ M₂ B false a e)).sum) =
        (p.edges.map (fun a => cost (arcPoint M₁ M₂ B false a))).sum := by
      simp only [cost, linearTotal_apply]
      simp_rw [← List.sum_map_mul_left]
      rw [sum_list_swap]
    simp only [cost, linearTotal_apply, z]
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, hswap]
    have hm : (p.edges.map (fun a => cost (arcPoint M₁ M₂ B false a))).sum =
        p.edges.length * cost (point B) -
          (W : ℝ) := by
      simp only [hdrop, W, Maths.MaxPlusPotential.walkWeight]
      induction p.edges with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
          Nat.cast_one, Int.cast_add] at *
        linarith
    rw [hm]
    rw [← linearTotal_apply]
    change (cost (point B) + ((p.edges.length : ℝ) * cost (point B) -
      (W : ℝ))) / k = cost (point B) - (W : ℝ) / k
    apply (div_eq_iff hk.ne').mpr
    rw [sub_mul, div_mul_cancel₀ _ hk.ne']
    dsimp [k]
    ring
  rw [hcavg] at hcost
  have hnonpos : (W : ℝ) ≤ 0 := by
    have : (W : ℝ) / k ≤ 0 := by linarith
    have h := (div_le_iff₀ hk).mp this
    simpa only [zero_mul] using h
  exact_mod_cast hnonpos

#print axioms optimal_common_base_closedWalk_nonpos

/-- Finite native matroids with a common base admit an integral split with the same
base optimal for both summands. The split equality holds on the whole carrier. -/
theorem finite_integral_weight_splitting (M₁ M₂ : Matroid E)
    (hE : M₁.E = M₂.E) (hcommon : ∃ B, M₁.IsBase B ∧ M₂.IsBase B) (w : E → ℤ) :
    ∃ (B : Set E) (c d : E → ℤ), M₁.IsBase B ∧ M₂.IsBase B ∧
      (∀ e, c e + d e = w e) ∧
      (∀ C, M₁.IsBase C → weightSum c B ≤ weightSum c C) ∧
      (∀ D, M₂.IsBase D → weightSum d B ≤ weightSum d D) := by
  classical
  let bases : Set (Set E) := {B | M₁.IsBase B ∧ M₂.IsBase B}
  obtain ⟨B, hB, hmin⟩ := Set.exists_min_image bases (weightSum w) (Set.toFinite bases) hcommon
  have hcyc := optimal_common_base_closedWalk_nonpos M₁ M₂ hE w hB.1 hB.2
    (fun C hC₁ hC₂ => hmin C ⟨hC₁, hC₂⟩)
  haveI : Finite (ExchangeArc M₁ M₂ B) := by unfold ExchangeArc; infer_instance
  obtain ⟨φ, hφ⟩ :=
    (Maths.MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos
      (G := exchangeGraph M₁ M₂ B) (exchangeWeight M₁ M₂ B w)).mpr hcyc
  refine ⟨B, φ, (fun e => w e - φ e), hB.1, hB.2, (fun e => by dsimp; omega), ?_, ?_⟩
  · apply exchange_local_is_global_minimum M₁ φ hB.1
    intro b hb e he hex
    let a : ExchangeArc M₁ M₂ B := ⟨(true, b, e), hb, he, hex⟩
    have h := hφ a
    simpa only [Maths.MaxPlusPotential.IsPotential, exchangeGraph, exchangeWeight,
      a, ite_true, add_zero] using h
  · apply exchange_local_is_global_minimum M₂ (fun e => w e - φ e) hB.2
    intro b hb e he hex
    have he₁ : e ∈ M₁.E \ B := ⟨hE.symm ▸ he.1, he.2⟩
    let a : ExchangeArc M₁ M₂ B := ⟨(false, b, e), hb, he₁, hex⟩
    have h := hφ a
    simp only [exchangeGraph, exchangeWeight, a, Bool.false_eq_true, ite_false] at h
    omega

#print axioms finite_integral_weight_splitting

end D5.S3.Combinatorics.Matroids.IntegralWeightSplitting
