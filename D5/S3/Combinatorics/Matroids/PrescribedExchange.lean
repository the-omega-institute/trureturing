/- GID: D5/S3/Combinatorics/Matroids/PrescribedExchange
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/PrescribedExchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simultaneous prescribed base exchanges obey the native rank bound. -/

import D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation
import D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierDual
import D5.S3.Combinatorics.Matroids.FiniteIntersectionPolytope
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Tactic.Tauto

/-! # Integral base optimality and weight splitting -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Matroids.PrescribedExchange

open scoped BigOperators
open Set Matroid

universe u
variable {E : Type u} [Finite E]

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual integral finite sum over a set of carrier elements. -/
private noncomputable def weightSum (q : E → ℤ) (B : Set E) : ℤ :=
  ∑ e ∈ B.toFinite.toFinset, q e

/-- Single-element exchange optimality implies optimality against every native base. -/
private theorem exchange_local_is_global_minimum (M : Matroid E) (q : E → ℤ)
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


/-- Tagged native exchanges; `true` tags the first matroid. -/
private def ExchangeArc (M₁ M₂ : Matroid E) (B : Set E) :=
  {a : Bool × E × E // a.2.1 ∈ B ∧ a.2.2 ∈ M₁.E \ B ∧
    (if a.1 = true then M₁ else M₂).IsBase (insert a.2.2 (B \ {a.2.1}))}

/-- The first matroid is oriented inside-to-outside and the second in reverse. -/
private def exchangeGraph (M₁ M₂ : Matroid E) (B : Set E) :
    Maths.EdgeGraph E (ExchangeArc M₁ M₂ B) where
  source a := if a.val.1 = true then a.val.2.1 else a.val.2.2
  target a := if a.val.1 = true then a.val.2.2 else a.val.2.1

/-- The asymmetric integral arc weight in the closed-walk obstruction. -/
private def exchangeWeight (M₁ M₂ : Matroid E) (B : Set E) (w : E → ℤ)
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
  let weight (a : ExchangeArc M₁ M₂ B) :=
    arcPoint M₁ M₂ B true a x - arcPoint M₁ M₂ B false a x
  let φ (v : E) := point {v} x
  have hedge (a : ExchangeArc M₁ M₂ B) :
      weight a = φ ((exchangeGraph M₁ M₂ B).target a) -
        φ ((exchangeGraph M₁ M₂ B).source a) := by
    have hex := point_exchange a.property.1 a.property.2.1.2 x
    cases ht : a.val.1 <;>
      simp only [weight, φ, exchangeGraph, arcPoint, ht, Bool.false_eq_true,
        Bool.true_eq_false, ite_false, ite_true] <;> linarith
  have hpos : Maths.MaxPlusPotential.IsPotential (exchangeGraph M₁ M₂ B) weight φ := by
    intro a
    rw [hedge]
    linarith
  have hneg : Maths.MaxPlusPotential.IsPotential (exchangeGraph M₁ M₂ B)
      (fun a => -weight a) (fun v => -φ v) := by
    intro a
    change -φ ((exchangeGraph M₁ M₂ B).source a) + -weight a ≤
      -φ ((exchangeGraph M₁ M₂ B).target a)
    rw [hedge]
    linarith
  have hp := hpos.walkWeight_add_le p
  have hn := hneg.walkWeight_add_le p
  have hnegmap (f : ExchangeArc M₁ M₂ B → ℝ) :
      (p.edges.map (fun a => -f a)).sum = -(p.edges.map f).sum := by
    simpa only [List.map_map, Function.comp_def] using
      (List.sum_neg (p.edges.map f)).symm
  have hsum : Maths.MaxPlusPotential.walkWeight weight p =
      (p.edges.map (fun a => arcPoint M₁ M₂ B true a x)).sum -
        (p.edges.map (fun a => arcPoint M₁ M₂ B false a x)).sum := by
    simp only [Maths.MaxPlusPotential.walkWeight, weight, sub_eq_add_neg,
      List.sum_map_add, hnegmap]
  have hnsum : Maths.MaxPlusPotential.walkWeight (fun a => -weight a) p =
      -Maths.MaxPlusPotential.walkWeight weight p := by
    exact hnegmap weight
  rw [hsum] at hp
  rw [hnsum, hsum] at hn
  dsimp [φ] at hp hn
  linarith

private lemma sum_list_swap {A : Type*} (l : List A) (f : A → E → ℝ) (U : Finset E) :
    (∑ e ∈ U, (l.map (fun a => f a e)).sum) =
      (l.map (fun a => ∑ e ∈ U, f a e)).sum := by
  simpa using (Multiset.sum_map_sum (m := (l : Multiset A)) (s := U) (f := f)).symm

private lemma list_bound {A : Type*} (l : List A) (f : A → ℝ) (r : ℝ)
    (hf : ∀ a ∈ l, f a ≤ r) : (l.map f).sum ≤ l.length * r := by
  have h := List.sum_le_length_nsmul (l.map f) r (by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact hf a ha)
  simpa only [List.length_map, nsmul_eq_mul] using h

/-- An optimal common base has no positive closed walk in the tagged exchange graph. -/
private theorem optimal_common_base_closedWalk_nonpos (M₁ M₂ : Matroid E)
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


/-- Finite native matroids with a common base admit an integral split with the same
base optimal for both summands. The split equality holds on the whole carrier. -/
private theorem finite_integral_weight_splitting (M₁ M₂ : Matroid E)
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


private noncomputable abbrev rk (M : Matroid E) (S : Set E) : ℕ := (M.eRk S).toNat

private lemma integer_threshold (M : Matroid E) (c : E → ℤ) {C : Set E}
    (hC : M.IsBase C) (hmin : ∀ D, M.IsBase D → weightSum c C ≤ weightSum c D)
    (t : ℤ) : (C ∩ {e | e ∈ M.E ∧ c e ≤ t}).ncard =
      rk M {e | e ∈ M.E ∧ c e ≤ t} := by
  have hm : ∀ D, M.IsBase D →
      NativeWeightedBaseRankSaturation.baseWeight (fun e => (c e : ℝ)) C ≤
        NativeWeightedBaseRankSaturation.baseWeight (fun e => (c e : ℝ)) D := by
    intro D hD
    have h := hmin D hD
    unfold weightSum at h
    unfold NativeWeightedBaseRankSaturation.baseWeight
    dsimp only
    exact_mod_cast h
  have h := ((NativeWeightedBaseRankSaturation.native_weighted_base_rank_saturation
    M (fun e => (c e : ℝ))).2 C hC).mp hm (t : ℝ)
  simpa only [NativeWeightedBaseRankSaturation.lowerWeightSet, Int.cast_le] using h

private lemma minor_rank_add (M : Matroid E) {X Y S : Set E}
    (hS : S ⊆ (M ／ X ＼ Y).E) (hX : M.Indep X) :
    rk (M ／ X ＼ Y) S + X.ncard = rk M (S ∪ X) := by
  change ((M ／ X ＼ Y).eRk S).toNat + X.ncard = (M.eRk (S ∪ X)).toNat
  have hS' : S ⊆ (M ／ X).E \ Y := hS
  rw [delete_eq_restrict, restrict_eRk_eq (M ／ X) hS']
  rw [← ENat.natCast_inj, Nat.cast_add, FiniteIntersection.cast_toNat_eRk,
    FiniteIntersection.cast_toNat_eRk, (toFinite X).cast_ncard_eq,
    ← hX.eRk_eq_encard]
  exact FiniteIntersection.contract_eRk_add M X S

private lemma indep_size_le_rank (M : Matroid E) {I S : Set E}
    (hI : M.Indep I) (hIS : I ⊆ S) : I.ncard ≤ rk M S := by
  rw [← ENat.natCast_le_natCast, FiniteIntersection.cast_toNat_eRk,
    (toFinite I).cast_ncard_eq]
  exact hI.encard_le_eRk_of_subset hIS

private lemma partition_card {A B S : Set E} (hAB : Disjoint A B)
    (hS : S ⊆ A ∪ B) : S.ncard = (A ∩ S).ncard + (B ∩ S).ncard := by
  have heq : S = (A ∩ S) ∪ (B ∩ S) := by tauto_set
  exact (congrArg Set.ncard heq).trans
    (ncard_union_eq (hAB.mono inter_subset_left inter_subset_left))

set_option maxHeartbeats 1000000 in
-- The paired submodular calculation carries several native rank and set expressions.
/-- Two submodular squares telescope along the interleaved split-weight profiles. -/
private lemma profile_step (M : Matroid E) {A B X Y C T S : Set E}
    (hA : M.Indep A) (hB : M.Indep B) (hAB : Disjoint A B)
    (hX : X ⊆ A) (hY : Y ⊆ B)
    (hT : T ⊆ S) (hS : S ⊆ (A ∪ B) \ (X ∪ Y))
    (hp : rk M (S ∪ X) = X.ncard + (C ∩ S).ncard)
    (hq : rk M (((A ∩ S) ∪ (B ∩ T)) ∪ Y) +
      (C ∩ ((A ∩ S) ∪ (B ∩ T))).ncard =
      Y.ncard + ((A ∩ S) ∪ (B ∩ T)).ncard) :
    rk M (S ∪ (X ∪ Y)) + (B ∩ (C ∩ T)).ncard ≤
      rk M (T ∪ (X ∪ Y)) + (B ∩ (C ∩ S)).ncard := by
  let H := (A ∩ S) ∪ (B ∩ T)
  have hHS : H ⊆ S := union_subset inter_subset_right (inter_subset_right.trans hT)
  have hTH : T ⊆ H := by
    intro e he
    rcases (hS (hT he)).1 with ha | hb
    · exact Or.inl ⟨ha, hT he⟩
    · exact Or.inr ⟨hb, he⟩
  have hs₁ := FiniteIntersection.rank_submod M (S ∪ X) (H ∪ (X ∪ Y))
  have hs₂ := FiniteIntersection.rank_submod M (H ∪ Y) (T ∪ (X ∪ Y))
  have he₁ : (S ∪ X) ∩ (H ∪ (X ∪ Y)) = H ∪ X := by
    ext e
    have hh := @hHS e
    have hy : e ∈ Y → e ∉ S := fun hy hs => (hS hs).2 (Or.inr hy)
    simp only [mem_inter_iff, mem_union] at *
    tauto
  have he₂ : (H ∪ Y) ∩ (T ∪ (X ∪ Y)) = T ∪ Y := by
    ext e
    have hh := @hTH e
    have hx : e ∈ X → e ∉ H := fun hx hh => (hS (hHS hh)).2 (Or.inl hx)
    simp only [mem_inter_iff, mem_union] at *
    tauto
  have hu₁ : (S ∪ X) ∪ (H ∪ (X ∪ Y)) = S ∪ (X ∪ Y) := by
    ext e
    have hh := @hHS e
    simp only [mem_union]
    tauto
  have hu₂ : (H ∪ Y) ∪ (T ∪ (X ∪ Y)) = H ∪ (X ∪ Y) := by
    ext e
    have hh := @hTH e
    simp only [mem_union]
    tauto
  rw [he₁, hu₁] at hs₁
  rw [he₂, hu₂] at hs₂
  have hdx : Disjoint (A ∩ S) X := by
    exact disjoint_left.mpr (by intro e he hx; exact (hS he.2).2 (Or.inl hx))
  have hdy : Disjoint (B ∩ T) Y := by
    exact disjoint_left.mpr (by intro e he hy; exact (hS (hT he.2)).2 (Or.inr hy))
  have hl₁ := indep_size_le_rank M
    (hA.subset (union_subset (inter_subset_left) hX))
    (show (A ∩ S) ∪ X ⊆ H ∪ X from union_subset_union subset_union_left subset_rfl)
  have hl₂ := indep_size_le_rank M
    (hB.subset (union_subset inter_subset_left hY))
    (show (B ∩ T) ∪ Y ⊆ T ∪ Y from union_subset_union inter_subset_right subset_rfl)
  rw [ncard_union_eq hdx] at hl₁
  rw [ncard_union_eq hdy] at hl₂
  have hh : H.ncard = (A ∩ S).ncard + (B ∩ T).ncard :=
    ncard_union_eq (hAB.mono inter_subset_left inter_subset_left)
  have hch : (C ∩ H).ncard = (A ∩ (C ∩ S)).ncard + (B ∩ (C ∩ T)).ncard := by
    have heq : C ∩ H = (A ∩ (C ∩ S)) ∪ (B ∩ (C ∩ T)) := by
      ext e
      simp only [H, mem_inter_iff, mem_union]
      tauto
    rw [heq, ncard_union_eq (hAB.mono inter_subset_left inter_subset_left)]
  have hcs := partition_card hAB (show C ∩ S ⊆ A ∪ B from
    inter_subset_right.trans (hS.trans sdiff_subset))
  change rk M (H ∪ Y) + (C ∩ H).ncard = Y.ncard + H.ncard at hq
  simp only [rk] at hp hq hl₁ hl₂ ⊢
  omega

private lemma dual_rank_add (M : Matroid E) {S : Set E} (hS : S ⊆ M.E) :
    rk M✶ S + rk M M.E = rk M (M.E \ S) + S.ncard := by
  rw [← ENat.natCast_inj, Nat.cast_add, Nat.cast_add,
    FiniteIntersection.cast_toNat_eRk, FiniteIntersection.cast_toNat_eRk,
    FiniteIntersection.cast_toNat_eRk, (toFinite S).cast_ncard_eq]
  simpa only [eRank_def] using M.eRk_dual_add_eRank S hS

set_option maxHeartbeats 1000000 in
-- Threshold complementation and telescoping use both residual matroids simultaneously.
private lemma paired_rank_bound (M : Matroid E) {A B X Y C : Set E}
    (hA : M.IsBase A) (hB : M.IsBase B) (hAB : Disjoint A B)
    (hE : M.E = A ∪ B) (hX : X ⊆ A) (hY : Y ⊆ B)
    (hdualA : M✶.IsBase A)
    (hP : (M ／ X ＼ Y).IsBase C) (hQ : (M✶ ／ X ＼ Y).IsBase C)
    (hP₀ : (M ／ X ＼ Y).IsBase (A \ X))
    (c d : E → ℤ) (hsplit : ∀ e, c e + d e = if e ∈ A \ X then 1 else 0)
    (hminP : ∀ D, (M ／ X ＼ Y).IsBase D → weightSum c C ≤ weightSum c D)
    (hminQ : ∀ D, (M✶ ／ X ＼ Y).IsBase D → weightSum d C ≤ weightSum d D) :
    (A ∩ C).ncard + X.ncard ≤ rk M (X ∪ Y) := by
  classical
  let R := (A ∪ B) \ (X ∪ Y)
  have hPR : (M ／ X ＼ Y).E = R := by
    ext e
    simp only [delete_ground, contract_ground, hE, R, mem_sdiff, mem_union]
    tauto
  have hQR : (M✶ ／ X ＼ Y).E = R := by
    simpa only [delete_ground, contract_ground, dual_ground] using hPR
  have hCR : C ⊆ R := hPR ▸ hP.subset_ground
  have hRX : Disjoint R X := disjoint_left.mpr (by
    intro e he hx; exact he.2 (Or.inl hx))
  have hRY : Disjoint R Y := disjoint_left.mpr (by
    intro e he hy; exact he.2 (Or.inr hy))
  have hXY : Disjoint X Y := hAB.mono hX hY
  have hCcard : C.ncard + X.ncard = A.ncard := by
    rw [hP.ncard_eq_ncard_of_isBase hP₀]
    exact ncard_sdiff_add_ncard_of_subset hX
  have hRcard : R.ncard + X.ncard + Y.ncard = A.ncard + A.ncard := by
    have hu : R ∪ (X ∪ Y) = A ∪ B := by
      exact sdiff_union_of_subset (union_subset_union hX hY)
    have hr := congrArg Set.ncard hu
    rw [ncard_union_eq disjoint_sdiff_left, ncard_union_eq hXY,
      ncard_union_eq hAB, ← hA.ncard_eq_ncard_of_isBase hB] at hr
    change R.ncard + (X.ncard + Y.ncard) = A.ncard + A.ncard at hr
    omega
  have hRank : rk M M.E = A.ncard := by
    rw [rk, ← eRank_def, ← hA.encard_eq_eRank, ncard_def]
  let S : ℤ → Set E := fun t => {e | e ∈ R ∧ c e ≤ t}
  have hSS (t : ℤ) : S (t - 1) ⊆ S t := by
    intro e he
    exact ⟨he.1, le_trans he.2 (by omega)⟩
  have hSR (t : ℤ) : S t ⊆ R := fun _ he => he.1
  have hp (t : ℤ) : rk M (S t ∪ X) = X.ncard + (C ∩ S t).ncard := by
    have hs := integer_threshold (M ／ X ＼ Y) c hP hminP t
    have he : {e | e ∈ (M ／ X ＼ Y).E ∧ c e ≤ t} = S t := by rw [hPR]
    rw [he] at hs
    have hr := minor_rank_add M (hPR.symm ▸ hSR t) (hA.indep.subset hX)
    omega
  have hq (t : ℤ) :
      rk M (((A ∩ S t) ∪ (B ∩ S (t - 1))) ∪ Y) +
        (C ∩ ((A ∩ S t) ∪ (B ∩ S (t - 1)))).ncard =
      Y.ncard + ((A ∩ S t) ∪ (B ∩ S (t - 1))).ncard := by
    let H := (A ∩ S t) ∪ (B ∩ S (t - 1))
    let K := R \ H
    have hHR : H ⊆ R := union_subset (inter_subset_right.trans (hSR t))
      (inter_subset_right.trans (hSR (t-1)))
    have hKR : K ⊆ R := sdiff_subset
    have hcut : {e | e ∈ (M✶ ／ X ＼ Y).E ∧ d e ≤ -t} = K := by
      ext e
      have hz := hsplit e
      have hab : e ∈ R → e ∈ A ∨ e ∈ B := fun he => he.1
      have hnx : e ∈ R → e ∉ X := fun he hx => he.2 (Or.inl hx)
      have hd := disjoint_left.mp hAB
      simp only [hQR, K, H, S, mem_setOf_eq, mem_sdiff, mem_union, mem_inter_iff]
      by_cases he : e ∈ R
      · rcases hab he with ha | hb
        · have hb : e ∉ B := fun hb => hd ha hb
          simp only [mem_sdiff, ha, hnx he, not_false_eq_true, and_self,
            ite_true] at hz
          simp only [he, ha, hb, true_and, false_and, or_false, and_true]
          omega
        · have ha : e ∉ A := fun ha => hd ha hb
          simp only [mem_sdiff, ha, false_and, ite_false] at hz
          simp only [he, ha, hb, true_and, false_and, false_or, and_true]
          omega
      · simp [he]
    have hs := integer_threshold (M✶ ／ X ＼ Y) d hQ hminQ (-t)
    rw [hcut] at hs
    have hm := minor_rank_add M✶ (hQR.symm ▸ hKR) (hdualA.indep.subset hX)
    have hkx : Disjoint K X := hRX.mono_left hKR
    have hku : (K ∪ X).ncard = K.ncard + X.ncard := ncard_union_eq hkx
    have hcomp : M.E \ (K ∪ X) = H ∪ Y := by
      ext e
      have hx := @hX e
      have hy := @hY e
      have hh := @hHR e
      have hd : ¬ (e ∈ X ∧ e ∈ Y) := fun he => disjoint_left.mp hXY he.1 he.2
      simp only [hE, R, K, mem_sdiff, mem_union] at hh ⊢
      tauto
    have hd := dual_rank_add M (show K ∪ X ⊆ M.E from
      union_subset (hKR.trans (sdiff_subset.trans (hE.symm ▸ subset_rfl)))
        (hX.trans hA.subset_ground))
    rw [hcomp, hku, hRank] at hd
    have hck : (C ∩ K).ncard + (C ∩ H).ncard = C.ncard := by
      have heq : C ∩ K = C \ H := by
        ext e
        have hh := @hCR e
        simp only [K, mem_inter_iff, mem_sdiff]
        tauto
      rw [heq, add_comm]
      exact ncard_inter_add_ncard_sdiff_eq_ncard C H
    have hkh : K.ncard + H.ncard = R.ncard := ncard_sdiff_add_ncard_of_subset hHR
    change rk M (H ∪ Y) + (C ∩ H).ncard = Y.ncard + H.ncard
    omega
  have hstep (t : ℤ) := profile_step M hA.indep hB.indep hAB hX hY
    (hSS t) (hSR t) (hp t) (hq t)
  obtain ⟨lo, hlo⟩ := ((toFinite R).image c).bddBelow
  obtain ⟨hi, hhi⟩ := ((toFinite R).image c).bddAbove
  have hlo' : ∀ e ∈ R, lo ≤ c e := by
    intro e he; exact hlo (mem_image_of_mem c he)
  have hhi' : ∀ e ∈ R, c e ≤ hi := by
    intro e he; exact hhi (mem_image_of_mem c he)
  let n := (max hi lo - lo + 1).toNat
  have hn : (n : ℤ) = max hi lo - lo + 1 := Int.toNat_of_nonneg (by omega)
  have hbottom : S (lo - 1) = ∅ := by
    ext e
    simp only [S, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro he
    have := hlo' e he
    omega
  have htop : S (lo - 1 + n) = R := by
    ext e
    constructor
    · exact fun he => he.1
    · intro he
      exact ⟨he, by have := hhi' e he; omega⟩
  have htel (k : ℕ) :
      rk M (S (lo - 1 + k) ∪ (X ∪ Y)) ≤
        rk M (X ∪ Y) + (B ∩ (C ∩ S (lo - 1 + k))).ncard := by
    induction k with
    | zero => simp [hbottom]
    | succ k ih =>
      have hs := hstep (lo - 1 + (k+1))
      simp only [Nat.cast_add, Nat.cast_one] at hs ⊢
      have he : lo - 1 + ((k : ℤ) + 1) - 1 = lo - 1 + k := by omega
      rw [he] at hs
      omega
  have ht := htel n
  rw [htop] at ht
  have heq : R ∪ (X ∪ Y) = M.E := by
    rw [hE]
    exact sdiff_union_of_subset (union_subset_union hX hY)
  have hci : C ∩ R = C := inter_eq_left.mpr hCR
  rw [heq, hRank, hci] at ht
  have hc := partition_card hAB (hCR.trans sdiff_subset)
  omega

private lemma normalize_bases (M : Matroid E) {A B : Set E} (hA : M.IsBase A) (hB : M.IsBase B) :
    let I := A ∩ B
    let R := (A ∪ B) \ I
    let N := (M ／ I) ↾ R
    N.IsBase (A \ B) ∧ N.IsBase (B \ A) ∧
      N.E = (A \ B) ∪ (B \ A) ∧ Disjoint (A \ B) (B \ A) := by
  classical
  dsimp only
  have hI : M.Indep (A ∩ B) := hA.indep.subset inter_subset_left
  have hca : (M ／ (A ∩ B)).IsBase (A \ B) := by
    apply hI.contract_isBase_iff.mpr
    constructor
    · convert hA using 1 <;> ext e <;> simp only [mem_union, mem_sdiff, mem_inter_iff] <;> tauto
    · exact Set.disjoint_left.mpr (by intro e he hf; exact he.2 hf.2)
  have hcb : (M ／ (A ∩ B)).IsBase (B \ A) := by
    apply hI.contract_isBase_iff.mpr
    constructor
    · convert hB using 1 <;> ext e <;> simp only [mem_union, mem_sdiff, mem_inter_iff] <;> tauto
    · exact Set.disjoint_left.mpr (by intro e he hf; exact he.2 hf.1)
  have hR : (A ∪ B) \ (A ∩ B) ⊆ (M ／ (A ∩ B)).E := by
    rw [contract_ground]
    exact sdiff_subset_sdiff_left (union_subset hA.subset_ground hB.subset_ground)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (isBase_restrict_iff hR).mpr
    exact hca.isBasis_ground.isBasis_subset (by intro e he; exact ⟨Or.inl he.1, fun hf => he.2 hf.2⟩) hR
  · apply (isBase_restrict_iff hR).mpr
    exact hcb.isBasis_ground.isBasis_subset (by intro e he; exact ⟨Or.inr he.1, fun hf => he.2 hf.1⟩) hR
  · rw [restrict_ground_eq]
    ext e
    simp only [mem_union, mem_sdiff, mem_inter_iff]
    tauto
  · exact Set.disjoint_left.mpr (by intro e he hf; exact he.2 hf.1)

private lemma reconstruct_exchange (N : Matroid E) {A B X Y C : Set E}
    (hA : N.IsBase A) (hB : N.IsBase B)
    (hAB : Disjoint A B) (hE : N.E = A ∪ B)
    (hX : X ⊆ A \ B) (hY : Y ⊆ B \ A)
    (hC1 : (N ／ X ＼ Y).IsBase C) (hC2 : (N✶ ／ X ＼ Y).IsBase C)
    (hcap : (A ∩ C).ncard + X.ncard ≤ (N.eRk (X ∪ Y)).toNat) :
    ∃ U V : Set E, U ⊆ A \ B ∧ V ⊆ B \ A ∧ X ⊆ U ∧ Y ⊆ V ∧
      U.ncard = V.ncard ∧ U.ncard ≤ (N.eRk (X ∪ Y)).toNat ∧
      N.IsBase ((A \ U) ∪ V) ∧ N.IsBase ((B \ V) ∪ U) := by
  classical
  have hd := disjoint_left.mp hAB
  have hXS : X ⊆ A := hX.trans sdiff_subset
  have hdualA : N✶.IsBase A := by
    convert hB.compl_isBase_dual using 1
    rw [hE]
    ext e
    simp only [mem_sdiff, mem_union]
    constructor
    · intro he; exact ⟨Or.inl he, fun hb => hd he hb⟩
    · tauto
  have lift {K : Matroid E} (hKE : K.E = N.E) (hKA : K.IsBase A) (hKC : (K ／ X ＼ Y).IsBase C) :
      K.IsBase (C ∪ X) := by
    have hu : (A \ X) ∪ X = A := sdiff_union_of_subset hXS
    have hc : (K ／ X).IsBase (A \ X) :=
      (hKA.indep.subset hXS).contract_isBase_iff.mpr
        ⟨by simpa only [hu] using hKA, disjoint_sdiff_left⟩
    have hYco : (K ／ X).Coindep Y := by
      apply coindep_iff_subset_compl_isBase.mpr
      refine ⟨A \ X, hc, ?_⟩
      intro e hy
      have hyA : e ∉ A := (hY hy).2
      refine ⟨?_, fun he => hyA he.1⟩
      rw [contract_ground]
      rw [hKE]
      exact ⟨hB.subset_ground (hY hy).1, fun hx => hyA (hXS hx)⟩
    exact ((hKA.indep.subset hXS).contract_isBase_iff.mp
      (hYco.delete_isBase_iff.mp hKC).1).1
  have hCG := hC1.subset_ground
  simp only [delete_ground, contract_ground] at hCG
  have hCN : C ⊆ A ∪ B := by
    intro e he
    exact hE ▸ (hCG he).1.1
  have hCX : Disjoint C X := disjoint_left.mpr (by intro e hc hx; exact (hCG hc).1.2 hx)
  have hCY : Disjoint C Y := disjoint_left.mpr (by intro e hc hy; exact (hCG hc).2 hy)
  have hH1 := lift rfl hA hC1
  have hH2 := (lift (show N✶.E = N.E from dual_ground) hdualA hC2).compl_isBase_of_dual
  let U := (A ∩ C) ∪ X
  let V := B \ C
  have hEq1 : (B \ V) ∪ U = C ∪ X := by
    ext e
    have hcn := @hCN e
    simp only [V, U, mem_union, mem_sdiff, mem_inter_iff] at hcn ⊢
    tauto
  have hEq2 : (A \ U) ∪ V = N.E \ (C ∪ X) := by
    rw [hE]
    ext e
    have hxa := @hXS e
    simp only [V, U, mem_union, mem_sdiff, mem_inter_iff]
    constructor
    · intro he
      rcases he with he | he
      · exact ⟨Or.inl he.1, by tauto⟩
      · exact ⟨Or.inr he.1, by intro hh; rcases hh with hh | hh; exact he.2 hh; exact hd (hxa hh) he.1⟩
    · tauto
  have hU : U ⊆ A \ B := by
    intro e he
    rcases he with he | he
    · exact ⟨he.1, fun hb => hd he.1 hb⟩
    · exact hX he
  have hV : V ⊆ B \ A := by
    intro e he
    exact ⟨he.1, fun ha => hd ha he.1⟩
  have hYV : Y ⊆ V := by
    intro e hy
    exact ⟨(hY hy).1, fun hc => disjoint_left.mp hCY hc hy⟩
  have hHdiff : (C ∪ X) \ B = U := by
    ext e
    have hcn := @hCN e
    have hxa := @hX e
    simp only [U, mem_sdiff, mem_union, mem_inter_iff] at *
    tauto
  have hBdiff : B \ (C ∪ X) = V := by
    ext e
    have hxa := @hX e
    simp only [V, mem_sdiff, mem_union] at *
    tauto
  have hcard := hB.ncard_sdiff_comm hH1
  rw [hHdiff, hBdiff] at hcard
  have hUcard : U.ncard = (A ∩ C).ncard + X.ncard :=
    ncard_union_eq (hCX.mono_left inter_subset_right)
  exact ⟨U, V, hU, hV, subset_union_right, hYV, hcard.symm,
    (by rw [hUcard]; exact hcap), (by rw [hEq2]; exact hH2),
    (by rw [hEq1]; exact hH1)⟩

private lemma lift_exchange (M : Matroid E) {A B U V : Set E}
    (hA : M.IsBase A) (hB : M.IsBase B)
    (hU : U ⊆ A \ B) (hV : V ⊆ B \ A)
    (hExA : ((M ／ (A ∩ B)) ↾ ((A ∪ B) \ (A ∩ B))).IsBase (((A \ B) \ U) ∪ V))
    (hExB : ((M ／ (A ∩ B)) ↾ ((A ∪ B) \ (A ∩ B))).IsBase (((B \ A) \ V) ∪ U)) :
    M.IsBase ((A \ U) ∪ V) ∧ M.IsBase ((B \ V) ∪ U) := by
  classical
  have hI : M.Indep (A ∩ B) := hA.indep.subset inter_subset_left
  have hca : (M ／ (A ∩ B)).IsBase (A \ B) := by
    apply hI.contract_isBase_iff.mpr
    constructor
    · convert hA using 1 <;> ext e <;> simp only [mem_union, mem_sdiff, mem_inter_iff] <;> tauto
    · exact Set.disjoint_left.mpr (by intro e he hf; exact he.2 hf.2)
  have hR : (A ∪ B) \ (A ∩ B) ⊆ (M ／ (A ∩ B)).E := by
    rw [contract_ground]
    exact sdiff_subset_sdiff_left (union_subset hA.subset_ground hB.subset_ground)
  have lift {C : Set E}
      (hC : ((M ／ (A ∩ B)) ↾ ((A ∪ B) \ (A ∩ B))).IsBase C) :
      M.IsBase (C ∪ (A ∩ B)) := by
    have hcb : (M ／ (A ∩ B)).IsBase C :=
      ((isBase_restrict_iff hR).mp hC).isBase_of_isBase_subset hca
        (by intro e he; exact ⟨Or.inl he.1, fun hf => he.2 hf.2⟩)
    exact (hI.contract_isBase_iff.mp hcb).1
  have hLA := lift hExA
  have hLB := lift hExB
  have hEqA : (((A \ B) \ U) ∪ V) ∪ (A ∩ B) = (A \ U) ∪ V := by
    ext e
    have hu := @hU e
    simp only [mem_union, mem_sdiff, mem_inter_iff] at hu ⊢
    tauto
  have hEqB : (((B \ A) \ V) ∪ U) ∪ (A ∩ B) = (B \ V) ∪ U := by
    ext e
    have hv := @hV e
    simp only [mem_union, mem_sdiff, mem_inter_iff] at hv ⊢
    tauto
  exact ⟨by simpa only [hEqA] using hLA, by simpa only [hEqB] using hLB⟩

private lemma disjoint_prescribed_exchange (N : Matroid E) {A B X Y : Set E}
    (hA : N.IsBase A) (hB : N.IsBase B)
    (hAB : Disjoint A B) (hE : N.E = A ∪ B)
    (hX : X ⊆ A \ B) (hY : Y ⊆ B \ A) :
    ∃ U V : Set E, U ⊆ A \ B ∧ V ⊆ B \ A ∧ X ⊆ U ∧ Y ⊆ V ∧
      U.ncard = V.ncard ∧ U.ncard ≤ (N.eRk (X ∪ Y)).toNat ∧
      N.IsBase ((A \ U) ∪ V) ∧ N.IsBase ((B \ V) ∪ U) := by
  classical
  have hdualA : N✶.IsBase A := by
    convert hB.compl_isBase_dual using 1
    rw [hE]
    ext e
    simp only [mem_sdiff, mem_union]
    have hd := Set.disjoint_left.mp hAB
    constructor
    · intro he; exact ⟨Or.inl he, fun hb => hd he hb⟩
    · tauto
  have hXS : X ⊆ A := hX.trans sdiff_subset
  have hdisj : Disjoint (A \ X) X := disjoint_sdiff_left
  have hu : (A \ X) ∪ X = A := sdiff_union_of_subset hXS
  have hc1 : (N ／ X).IsBase (A \ X) :=
    (hA.indep.subset hXS).contract_isBase_iff.mpr ⟨by simpa only [hu] using hA, hdisj⟩
  have hc2 : (N✶ ／ X).IsBase (A \ X) :=
    (hdualA.indep.subset hXS).contract_isBase_iff.mpr ⟨by simpa only [hu] using hdualA, hdisj⟩
  have hCY : Disjoint (A \ X) Y := by
    exact disjoint_left.mpr (by intro e he hy; exact (hY hy).2 he.1)
  have del {K : Matroid E} (hc : K.IsBase (A \ X)) : (K ＼ Y).IsBase (A \ X) := by
    rw [delete_isBase_iff]
    exact hc.isBasis_ground.isBasis_subset (subset_sdiff.mpr ⟨hc.subset_ground, hCY⟩) sdiff_subset
  have hground : (N ／ X ＼ Y).E = (N✶ ／ X ＼ Y).E := by
    simp only [delete_ground, contract_ground, dual_ground]
  obtain ⟨C, c, d, hC1, hC2, hsplit, hmin1, hmin2⟩ :=
    finite_integral_weight_splitting
      (N ／ X ＼ Y) (N✶ ／ X ＼ Y) hground ⟨A \ X, del hc1, del hc2⟩
      (fun e => if e ∈ A \ X then 1 else 0)
  have hcap := paired_rank_bound N hA hB hAB hE hXS (hY.trans sdiff_subset)
    hdualA hC1 hC2 (del hc1) c d hsplit hmin1 hmin2
  exact reconstruct_exchange N hA hB hAB hE hX hY hC1 hC2 hcap

/-- Rank-bounded simultaneous prescribed exchange, for arbitrary finite native matroids. -/
theorem exists_prescribed_exchange (M : Matroid E) {A B X Y : Set E}
    (hA : M.IsBase A) (hB : M.IsBase B)
    (hX : X ⊆ A \ B) (hY : Y ⊆ B \ A) :
    ∃ U V : Set E, U ⊆ A \ B ∧ V ⊆ B \ A ∧ X ⊆ U ∧ Y ⊆ V ∧
      U.ncard = V.ncard ∧ U.ncard ≤ (M.eRk (X ∪ Y)).toNat ∧
      M.IsBase ((A \ U) ∪ V) ∧ M.IsBase ((B \ V) ∪ U) := by
  classical
  let I := A ∩ B
  let R := (A ∪ B) \ I
  let N := (M ／ I) ↾ R
  obtain ⟨ha, hb, hNE, hab⟩ := normalize_bases M hA hB
  have hx : X ⊆ (A \ B) \ (B \ A) := by
    intro e he
    exact ⟨hX he, fun hf => (hX he).2 hf.1⟩
  have hy : Y ⊆ (B \ A) \ (A \ B) := by
    intro e he
    exact ⟨hY he, fun hf => (hY he).2 hf.1⟩
  obtain ⟨U, V, hU, hV, hXU, hYV, hcard, hcap, hExA, hExB⟩ :=
    disjoint_prescribed_exchange N ha hb hab hNE hx hy
  have hUa : U ⊆ A \ B := hU.trans sdiff_subset
  have hVb : V ⊆ B \ A := hV.trans sdiff_subset
  have hSR : X ∪ Y ⊆ R := by
    intro e he
    rcases he with he | he
    · exact ⟨Or.inl (hX he).1, fun hf => (hX he).2 hf.2⟩
    · exact ⟨Or.inr (hY he).1, fun hf => (hY he).2 hf.1⟩
  have hrank : (N.eRk (X ∪ Y)).toNat ≤ (M.eRk (X ∪ Y)).toNat := by
    change (((M ／ I) ↾ R).eRk (X ∪ Y)).toNat ≤ _
    rw [restrict_eRk_eq _ hSR]
    have hadd : ((M ／ I).eRk (X ∪ Y)).toNat + (M.eRk I).toNat =
        (M.eRk ((X ∪ Y) ∪ I)).toNat := by
      rw [← ENat.natCast_inj, Nat.cast_add, FiniteIntersection.cast_toNat_eRk,
        FiniteIntersection.cast_toNat_eRk, FiniteIntersection.cast_toNat_eRk]
      exact FiniteIntersection.contract_eRk_add M I (X ∪ Y)
    have hle : (M.eRk ((X ∪ Y) ∪ I)).toNat ≤
        (M.eRk (X ∪ Y)).toNat + (M.eRk I).toNat := by
      rw [← ENat.natCast_le_natCast, Nat.cast_add, FiniteIntersection.cast_toNat_eRk,
        FiniteIntersection.cast_toNat_eRk, FiniteIntersection.cast_toNat_eRk]
      exact M.eRk_union_le_eRk_add_eRk (X ∪ Y) I
    omega
  obtain ⟨hLA, hLB⟩ := lift_exchange M hA hB hUa hVb hExA hExB
  exact ⟨U, V, hUa, hVb, hXU, hYV, hcard, hcap.trans hrank, hLA, hLB⟩

#print axioms exists_prescribed_exchange

end D5.S3.Combinatorics.Matroids.PrescribedExchange
