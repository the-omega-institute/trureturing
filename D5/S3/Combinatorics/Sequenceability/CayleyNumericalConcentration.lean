/- GID: D5/S3/Combinatorics/Sequenceability/CayleyNumericalConcentration
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/CayleyNumericalConcentration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Embedded numerical Cayley descent and original-colour structural readouts. -/

import D5.S3.Combinatorics.Sequenceability.CayleySubgroupConcentration
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Basic.Complex.BigOperators

/-! Numerical stopping and embedded subgroup descent for Section 4 of Bedert,
Bucić, Kravitz, Montgomery and Müyesser, arXiv:2508.18254v1. The imported
localization theorem is used without alteration. Neither symmetry nor normality
nor exclusion of the identity is assumed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Sequenceability.CayleyNumericalConcentration

open D5.S3.Combinatorics.Sequenceability.CayleySubgroupConcentration (density retained near_invariant_localization)

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Counting-measure numerical gap, with the directed right-multiplication
adjacency convention. This is stronger than an eigenvalue real-part bound. -/
def NumericalGap {K : Type*} [Group K] [Fintype K]
    (T : Finset K) (η : ℝ) : Prop :=
  ∀ f : K → ℝ, (∑ x : K, f x) = 0 →
    (∑ x : K, ∑ t ∈ T, f x * f (x * t)) ≤
      (1 - η) * (T.card : ℝ) * (∑ x : K, (f x) ^ 2)

/-- Ordered original-label edges; identity labels give loops, as intended. -/
def directedCut {K : Type*} [Group K] [Fintype K]
    (T X Y : Finset K) : ℕ :=
  ((X ×ˢ Y).filter (fun xy => xy.1⁻¹ * xy.2 ∈ T)).card

/-- Coordinates on a left coset, with the explicit membership convention. -/
def leftCosetMap {G : Type*} [Group G]
    (H : Subgroup G) (a : G) : H → {x : G // a⁻¹ * x ∈ H} :=
  fun h => ⟨a * (h : G), by simpa [mul_assoc] using h.property⟩

private theorem retained_mem {G : Type*} [Group G] [Fintype G]
    (S : Finset G) (H : Subgroup G) (t : H) :
    t ∈ retained S H ↔ (t : G) ∈ S := by simp [retained]

private theorem retained_card_le {G : Type*} [Group G] [Fintype G]
    (S : Finset G) (H : Subgroup G) : (retained S H).card ≤ S.card := by
  let f : {t // t ∈ retained S H} → {s // s ∈ S} := fun t =>
    ⟨t.val.val, (retained_mem S H t.val).mp t.property⟩
  have hf : Function.Injective f := by
    intro t u h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : {s // s ∈ S} => (v.val : G)) h
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

private theorem retained_top_card {G : Type*} [Group G] [Fintype G]
    (S : Finset G) : (retained S (⊤ : Subgroup G)).card = S.card := by
  apply Finset.card_bij (s := retained S (⊤ : Subgroup G)) (t := S)
    (fun (t : (⊤ : Subgroup G)) _ => (t : G))
  · intro t ht
    exact (retained_mem S ⊤ t).mp ht
  · intro t ht u hu h
    exact Subtype.ext h
  · intro s hs
    exact ⟨⟨s, Subgroup.mem_top s⟩, (retained_mem S ⊤ _).mpr hs, rfl⟩

private theorem density_pos {K : Type*} [Fintype K] [Nonempty K]
    (T : Finset K) (hT : T.Nonempty) : 0 < density T := by
  apply div_pos
  · exact_mod_cast hT.card_pos
  · exact_mod_cast Fintype.card_pos

/-- An actual failing quadratic form, including its nonzeroness, supplies every
vector hypothesis of the frozen localizer. No spectral assertion is used. -/
private theorem localize_failure {K : Type*} [Group K] [Fintype K]
    (T : Finset K) (hT : T.Nonempty)
    (η : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ (density T) ^ 2 / 1000)
    (hfail : ¬ NumericalGap T η) :
    ∃ L : Subgroup K, L ≠ ⊤ ∧
      (1 - 50 * η / (density T) ^ 2) * (T.card : ℝ) ≤
        ((retained T L).card : ℝ) := by
  classical
  simp only [NumericalGap, not_forall, not_imp, not_le] at hfail
  obtain ⟨f, hmean, hbad⟩ := hfail
  have hf : f ≠ 0 := by
    intro h
    subst f
    simpa using hbad
  let w : EuclideanSpace ℝ K := WithLp.toLp 2 f
  have hw : w ≠ 0 := by
    intro h
    apply hf
    funext x
    exact congrArg (fun z : EuclideanSpace ℝ K => z x) h
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hmass : (∑ x : K, (f x) ^ 2) = ‖w‖ ^ 2 := by
    simpa only [w, PiLp.toLp_apply] using (EuclideanSpace.real_norm_sq_eq w).symm
  let v : EuclideanSpace ℝ K := ‖w‖⁻¹ • w
  have hv : ‖v‖ = 1 := by
    rw [show v = ‖w‖⁻¹ • w from rfl, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  have hvx (x : K) : v x = ‖w‖⁻¹ * f x := by
    simp only [v, w, PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul]
  have hvmean : (∑ x : K, v x) = 0 := by
    simp_rw [hvx]
    rw [← Finset.mul_sum, hmean, mul_zero]
  have hcorr : (1 - η) * (T.card : ℝ) ≤
      ∑ t ∈ T, ∑ x : K, v x * v (x * t) := by
    have hscale : (∑ t ∈ T, ∑ x : K, v x * v (x * t)) =
        ‖w‖⁻¹ ^ 2 * (∑ x : K, ∑ t ∈ T, f x * f (x * t)) := by
      simp_rw [hvx]
      rw [Finset.sum_comm]
      simp_rw [show ∀ x t : K, (‖w‖⁻¹ * f x) * (‖w‖⁻¹ * f (x * t)) =
        ‖w‖⁻¹ ^ 2 * (f x * f (x * t)) by intros; ring]
      simp_rw [← Finset.mul_sum]
    rw [hscale]
    rw [hmass] at hbad
    calc
      (1 - η) * (T.card : ℝ) =
          ‖w‖⁻¹ ^ 2 * ((1 - η) * (T.card : ℝ) * ‖w‖ ^ 2) := by
            field_simp [hn.ne']
            <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbad.le (sq_nonneg _)
  exact near_invariant_localization T hT η hη0 hη v hv hvmean hcorr

/-- The stage lives in the original ambient group, and retains its original
labels exactly. The third field is needed for density at stage zero. -/
private structure DescentStage {G : Type*} [Group G] [Fintype G]
    (S : Finset G) (ε : ℝ) (j : ℕ) (H : Subgroup G) : Prop where
  retention : (1 - ε + ε / (2 : ℝ) ^ j) * (S.card : ℝ) ≤ (retained S H).card
  volume : (2 : ℝ) ^ j * (Fintype.card H : ℝ) ≤ Fintype.card G
  initial : j = 0 → H = ⊤

private theorem stage_estimates {G : Type*} [Group G] [Fintype G]
    (S : Finset G) (hS : S.Nonempty) (ε : ℝ) (hε : 0 < ε)
    (hεhalf : ε < (1 / 2 : ℝ)) (j : ℕ) (H : Subgroup G)
    (st : DescentStage S ε j H) :
    (retained S H).Nonempty ∧ density S ≤ density (retained S H) ∧
      50 * (ε * density S ^ 2 / 1000) / density (retained S H) ^ 2 ≤
        ε / (2 : ℝ) ^ (j + 1) := by
  let p := (2 : ℝ) ^ j
  let σ := density S
  let τ := density (retained S H)
  have hp : 0 < p := by dsimp [p]; positivity
  have hpone : 1 ≤ p := by dsimp [p]; exact one_le_pow₀ (by norm_num)
  have hs : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hg : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hh : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have hσ : 0 < σ := density_pos S hS
  have hd : (S.card : ℝ) / 2 < (retained S H).card := by
    have he : 0 < ε / p := div_pos hε hp
    have := st.retention
    change (1 - ε + ε / p) * (S.card : ℝ) ≤ _ at this
    have hcoef : (1 / 2 : ℝ) < 1 - ε + ε / p := by linarith
    exact lt_of_lt_of_le (by nlinarith [mul_lt_mul_of_pos_right hcoef hs]) this
  have hT : (retained S H).Nonempty := Finset.card_pos.mp (by exact_mod_cast (by linarith [hd] : (0 : ℝ) < (retained S H).card))
  have hτ : 0 < τ := density_pos _ hT
  have hσg : σ * Fintype.card G = S.card := div_mul_cancel₀ _ hg.ne'
  have hτh : τ * Fintype.card H = (retained S H).card := div_mul_cancel₀ _ hh.ne'
  have hpτ : p * (retained S H).card ≤ (Fintype.card G : ℝ) * τ := by
    have hv := mul_le_mul_of_nonneg_right st.volume hτ.le
    change p * (Fintype.card H : ℝ) * τ ≤ _ at hv
    calc
      p * ((retained S H).card : ℝ) = p * (τ * Fintype.card H) := by rw [hτh]
      _ ≤ (Fintype.card G : ℝ) * τ := by nlinarith [hv]
  have hweak : p * σ / 2 ≤ τ := by
    have := mul_le_mul_of_nonneg_left hd.le hp.le
    have hbound : p * (S.card : ℝ) ≤ 2 * (Fintype.card G : ℝ) * τ := by linarith
    rw [← hσg] at hbound
    have hcancel : p * σ ≤ 2 * τ := by
      apply (mul_le_mul_iff_left₀ hg).mp
      convert hbound using 1 <;> ring
    linarith
  have hdensity : σ ≤ τ := by
    by_cases hj : j = 0
    · have htop := st.initial hj
      subst H
      have htopcard : Fintype.card (⊤ : Subgroup G) = Fintype.card G := by
        simpa only [Nat.card_eq_fintype_card] using (Subgroup.card_top (G := G))
      change (S.card : ℝ) / Fintype.card G ≤
        ((retained S (⊤ : Subgroup G)).card : ℝ) / Fintype.card (⊤ : Subgroup G)
      rw [retained_top_card, htopcard]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have hp2 : 2 ≤ p := by dsimp [p]; rw [pow_succ]; linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hp2) hσ.le]
  have hsquared : p * σ ^ 2 / 10 ≤ τ ^ 2 := by
    have hsq := mul_self_le_mul_self (by positivity : 0 ≤ p * σ / 2) hweak
    have hpp : 0 ≤ p ^ 2 - p := by
      nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hpone)]
    have hprod := mul_nonneg hpp (sq_nonneg σ)
    nlinarith
  refine ⟨hT, hdensity, ?_⟩
  change 50 * (ε * σ ^ 2 / 1000) / τ ^ 2 ≤ ε / (2 : ℝ) ^ (j + 1)
  rw [div_le_div_iff₀ (sq_pos_of_pos hτ) (by positivity)]
  rw [pow_succ]
  change 50 * (ε * σ ^ 2 / 1000) * (p * 2) ≤ ε * τ ^ 2
  nlinarith [mul_le_mul_of_nonneg_left hsquared hε.le]

private theorem embedded_localization {G : Type*} [Group G] [Fintype G]
    (S : Finset G) (H : Subgroup G) (L : Subgroup H) (hL : L ≠ ⊤) :
    let H' := L.map H.subtype
    H' ≤ H ∧
      (retained (retained S H) L).card = (retained S H').card ∧
      2 * Fintype.card H' ≤ Fintype.card H ∧
      Fintype.card H' < Fintype.card H := by
  let H' := L.map H.subtype
  let e : L ≃* H' := L.equivMapOfInjective H.subtype Subtype.val_injective
  have he (x : L) : (e x : G) = ((x : H) : G) := rfl
  have hle : H' ≤ H := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.property
  have hret : (retained (retained S H) L).card = (retained S H').card := by
    apply Finset.card_bij (fun t _ => e t)
    · intro t ht
      simpa only [retained_mem, he] using ht
    · intro t ht u hu h
      exact e.injective h
    · intro u hu
      refine ⟨e.symm u, ?_, e.apply_symm_apply u⟩
      have hei : (((e.symm u : L) : H) : G) = (u : G) := by
        rw [← he, e.apply_symm_apply]
      simpa only [retained_mem, hei] using hu
  have hc : Fintype.card H' = Fintype.card L := (Fintype.card_congr e.toEquiv).symm
  have hi : 2 ≤ L.index := L.one_lt_index_of_ne_top hL
  have hmul : Fintype.card L * L.index = Fintype.card H := by
    simpa only [Nat.card_eq_fintype_card] using L.card_mul_index
  have hhalf : 2 * Fintype.card H' ≤ Fintype.card H := by
    rw [hc, ← hmul]
    calc
      2 * Fintype.card L = Fintype.card L * 2 := Nat.mul_comm _ _
      _ ≤ Fintype.card L * L.index := Nat.mul_le_mul_left _ hi
  refine ⟨hle, hret, hhalf, ?_⟩
  have hpos : 0 < Fintype.card H' := Fintype.card_pos
  change Fintype.card H' < Fintype.card H
  omega

private theorem numerical_descent {G : Type*} [Group G] [Fintype G]
    (S : Finset G) (hS : S.Nonempty) (ε : ℝ) (hε : 0 < ε)
    (hεhalf : ε < (1 / 2 : ℝ)) :
    ∃ H : Subgroup G,
      (1 - ε) * (S.card : ℝ) ≤ (retained S H).card ∧
      density S ≤ density (retained S H) ∧
      NumericalGap (retained S H) (ε * density S ^ 2 / 1000) := by
  let η := ε * density S ^ 2 / 1000
  have hσ : 0 < density S := density_pos S hS
  have hη : 0 < η := by dsimp [η]; positivity
  have descend (n : ℕ) : ∀ (j : ℕ) (H : Subgroup G), Fintype.card H = n →
      DescentStage S ε j H →
      ∃ K : Subgroup G, K ≤ H ∧
        (1 - ε) * (S.card : ℝ) ≤ (retained S K).card ∧
        density S ≤ density (retained S K) ∧ NumericalGap (retained S K) η := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j H hn st
      obtain ⟨hT, hτ, hloss⟩ := stage_estimates S hS ε hε hεhalf j H st
      by_cases hgap : NumericalGap (retained S H) η
      · refine ⟨H, le_rfl, ?_, hτ, hgap⟩
        have hs : 0 ≤ (S.card : ℝ) := by positivity
        have hx : 0 ≤ ε / (2 : ℝ) ^ j := by positivity
        nlinarith [st.retention, mul_nonneg hx hs]
      · have hβ : η ≤ density (retained S H) ^ 2 / 1000 := by
          have hτpos := density_pos _ hT
          have hsq := mul_self_le_mul_self hσ.le hτ
          have hepssq : ε * density S ^ 2 ≤ density S ^ 2 :=
            by simpa only [one_mul] using
              mul_le_mul_of_nonneg_right (by linarith : ε ≤ 1) (sq_nonneg (density S))
          dsimp [η]
          nlinarith
        obtain ⟨L, hL, hlabels⟩ := localize_failure (retained S H) hT η hη.le hβ hgap
        let H' := L.map H.subtype
        obtain ⟨hle, hcard, hhalf, hstrict⟩ := embedded_localization S H L hL
        have hnew : DescentStage S ε (j + 1) H' := by
          constructor
          · have hupper : ((retained S H).card : ℝ) ≤ S.card := by
              exact_mod_cast retained_card_le S H
            have hb : 0 ≤ ε / (2 : ℝ) ^ (j + 1) := by positivity
            have hloss' := mul_le_mul_of_nonneg_right hloss (show (0 : ℝ) ≤ (retained S H).card by positivity)
            have hbudget := mul_le_mul_of_nonneg_left hupper hb
            rw [hcard] at hlabels
            have hgeometric : ε / (2 : ℝ) ^ j = 2 * (ε / (2 : ℝ) ^ (j + 1)) := by
              rw [pow_succ]; field_simp <;> ring
            have hgeometric' := congrArg (fun r : ℝ => r * (S.card : ℝ)) hgeometric
            dsimp [η] at hlabels
            nlinarith [st.retention]
          · have hhR : 2 * (Fintype.card H' : ℝ) ≤ Fintype.card H := by exact_mod_cast hhalf
            have hhpow := mul_le_mul_of_nonneg_left hhR (show (0 : ℝ) ≤ 2 ^ j by positivity)
            rw [pow_succ]
            nlinarith [st.volume]
          · intro hj
            omega
        obtain ⟨K, hKH', hretain, hdense, hterminal⟩ :=
          ih (Fintype.card H') (hn ▸ hstrict) (j + 1) H' rfl hnew
        exact ⟨K, le_trans hKH' hle, hretain, hdense, hterminal⟩
  have hinit : DescentStage S ε 0 (⊤ : Subgroup G) := by
    constructor
    · simp [retained_top_card]
    · simp only [pow_zero, one_mul]
      exact_mod_cast (show Fintype.card (⊤ : Subgroup G) ≤ Fintype.card G from
        by simpa only [Nat.card_eq_fintype_card] using (Subgroup.card_top (G := G)).le)
    · intro _; rfl
  obtain ⟨H, _, hretain, hdense, hgap⟩ := descend _ 0 ⊤ rfl hinit
  exact ⟨H, hretain, hdense, hgap⟩

private def indicator {K : Type*} (X : Finset K) (x : K) : ℝ :=
  if x ∈ X then 1 else 0

private theorem indicator_sum {K : Type*} [Fintype K] (X : Finset K) :
    (∑ x : K, indicator X x) = X.card := by
  simp [indicator, Finset.sum_ite]

private theorem indicator_sq {K : Type*} (X : Finset K) (x : K) :
    indicator X x ^ 2 = indicator X x := by
  unfold indicator
  split_ifs <;> norm_num

private theorem partition_indicator {K : Type*} [Fintype K]
    (X Y : Finset K) (hdisj : Disjoint X Y) (hcover : X ∪ Y = Finset.univ) (x : K) :
    indicator Y x = 1 - indicator X x := by
  have hmem : x ∈ X ∨ x ∈ Y := by
    rw [← Finset.mem_union, hcover]
    exact Finset.mem_univ x
  have hnot : ¬ (x ∈ X ∧ x ∈ Y) := by
    rintro ⟨hx, hy⟩
    exact Finset.disjoint_left.mp hdisj hx hy
  by_cases hx : x ∈ X <;> by_cases hy : x ∈ Y <;> simp_all [indicator]

private theorem regular_sum {K : Type*} [Group K] [Fintype K]
    {R : Type*} [AddCommMonoid R] (f : K → R) (t : K) :
    (∑ x : K, f (x * t)) = ∑ x : K, f x := by
  exact Fintype.sum_equiv (Equiv.mulRight t) (fun x => f (x * t)) f (fun _ => rfl)

/-- The two exact directed edge encodings are related by (x,t) ↦ (x,xt).
The inverse keeps the original colour x⁻¹y. -/
private theorem directedCut_labelled {K : Type*} [Group K] [Fintype K]
    (T X Y : Finset K) :
    directedCut T X Y = ((X ×ˢ T).filter (fun xt => xt.1 * xt.2 ∈ Y)).card := by
  unfold directedCut
  symm
  apply Finset.card_bij (fun xt _ => (xt.1, xt.1 * xt.2))
  · intro xt hxt
    rcases Finset.mem_filter.mp hxt with ⟨hxt, hY⟩
    rcases Finset.mem_product.mp hxt with ⟨hX, hT⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hX, hY⟩, by simpa [mul_assoc] using hT⟩
  · intro xt hxt zu hzu heq
    rcases xt with ⟨x, t⟩
    rcases zu with ⟨y, u⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, ht⟩ := heq
    exact Prod.ext rfl (mul_left_cancel ht)
  · intro xy hxy
    rcases Finset.mem_filter.mp hxy with ⟨hxy, hT⟩
    rcases Finset.mem_product.mp hxy with ⟨hX, hY⟩
    refine ⟨(xy.1, xy.1⁻¹ * xy.2), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hX, hT⟩, by simpa [mul_assoc] using hY⟩
    · simp [mul_assoc]

private theorem directedCut_sum {K : Type*} [Group K] [Fintype K]
    (T X Y : Finset K) :
    (directedCut T X Y : ℝ) =
      ∑ x : K, ∑ t ∈ T, indicator X x * indicator Y (x * t) := by
  rw [directedCut_labelled, Finset.card_filter]
  push_cast
  rw [Finset.sum_product]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  calc
    (∑ x ∈ X, ∑ t ∈ T, if x * t ∈ Y then (1 : ℝ) else 0) =
        ∑ x ∈ X, ∑ t ∈ T, indicator Y (x * t) := rfl
    _ = ∑ x : K, ∑ t ∈ T, indicator X x * indicator Y (x * t) := by
      simp [indicator, ite_mul, Finset.sum_ite]

private theorem indicator_outgoing {K : Type*} [Group K] [Fintype K]
    (T X : Finset K) :
    (∑ x : K, ∑ _t ∈ T, indicator X x) = (T.card : ℝ) * X.card := by
  simp [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, indicator_sum]

private theorem indicator_incoming {K : Type*} [Group K] [Fintype K]
    (T X : Finset K) :
    (∑ x : K, ∑ t ∈ T, indicator X (x * t)) = (T.card : ℝ) * X.card := by
  rw [Finset.sum_comm]
  simp_rw [regular_sum, indicator_sum]
  simp

private theorem partition_card {K : Type*} [Fintype K]
    (X Y : Finset K) (hdisj : Disjoint X Y) (hcover : X ∪ Y = Finset.univ) :
    (X.card : ℝ) + Y.card = Fintype.card K := by
  have hnat : X.card + Y.card = Fintype.card K := by
    rw [← Finset.card_union_of_disjoint hdisj, hcover, Finset.card_univ]
  exact_mod_cast hnat

/-- Centered indicators give the numerical cut lower bound. Both orientations
are retained, and their equality comes from regular in/out counts. -/
private theorem numerical_cut {K : Type*} [Group K] [Fintype K]
    (T : Finset K) (η : ℝ) (hgap : NumericalGap T η)
    (X Y : Finset K) (hdisj : Disjoint X Y) (hcover : X ∪ Y = Finset.univ) :
    η * density T * (X.card : ℝ) * Y.card ≤ (directedCut T X Y : ℝ) ∧
      directedCut T X Y = directedCut T Y X := by
  let n : ℝ := Fintype.card K
  let x : ℝ := X.card
  let d : ℝ := T.card
  let c : ℝ := x / n
  let f : K → ℝ := fun u => indicator X u - c
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos
  have hcn : c * n = x := div_mul_cancel₀ _ hn.ne'
  have hsum : (∑ u : K, f u) = 0 := by
    simp only [f, Finset.sum_sub_distrib, indicator_sum, Finset.sum_const, nsmul_eq_mul]
    dsimp [c, x, n]
    field_simp [hn.ne']
    <;> ring
  have hmass : (∑ u : K, f u ^ 2) = x - x ^ 2 / n := by
    have he (u : K) : f u ^ 2 = indicator X u ^ 2 - 2 * c * indicator X u + c ^ 2 := by
      dsimp [f]; ring
    simp_rw [he, indicator_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, indicator_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    dsimp [x, c, n]
    field_simp [hn.ne']
    <;> ring
  have hquad : (∑ u : K, ∑ t ∈ T, f u * f (u * t)) =
      (directedCut T X X : ℝ) - d * x ^ 2 / n := by
    have he (u t : K) : f u * f (u * t) =
        indicator X u * indicator X (u * t) - c * indicator X u -
          c * indicator X (u * t) + c ^ 2 := by dsimp [f]; ring
    simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← directedCut_sum]
    simp_rw [← Finset.mul_sum]
    rw [indicator_outgoing, indicator_incoming]
    simp only [Finset.sum_const, nsmul_eq_mul]
    dsimp [c, d, x, n]
    field_simp [hn.ne']
    <;> ring
  have hout : (directedCut T X Y : ℝ) = d * x - directedCut T X X := by
    rw [directedCut_sum]
    simp_rw [partition_indicator X Y hdisj hcover, mul_sub, mul_one,
      Finset.sum_sub_distrib]
    rw [indicator_outgoing, ← directedCut_sum]
  have hin : (directedCut T Y X : ℝ) = d * x - directedCut T X X := by
    rw [directedCut_sum]
    simp_rw [partition_indicator X Y hdisj hcover, sub_mul, one_mul,
      Finset.sum_sub_distrib]
    rw [indicator_incoming, ← directedCut_sum]
  have hbalance : directedCut T X Y = directedCut T Y X := by exact_mod_cast hout.trans hin.symm
  refine ⟨?_, hbalance⟩
  have h := hgap f hsum
  rw [hmass, hquad] at h
  have hpart := partition_card X Y hdisj hcover
  have htarget : η * density T * (X.card : ℝ) * Y.card = η * d * (x - x ^ 2 / n) := by
    change η * (d / n) * x * (Y.card : ℝ) = η * d * (x - x ^ 2 / n)
    have hy : (Y.card : ℝ) = n - x := by dsimp [x, n]; linarith [hpart]
    rw [hy]
    field_simp [hn.ne']
    <;> ring
  change (directedCut T X X : ℝ) - d * x ^ 2 / n ≤
    (1 - η) * d * (x - x ^ 2 / n) at h
  rw [htarget, hout]
  linear_combination h

/-- Complex adjacency preserves the actual zero-sum space by right-translation
reindexing; this does not require normality of the operator. -/
private theorem adjacency_mean_zero {K : Type*} [Group K] [Fintype K]
    (T : Finset K) (z : K → ℂ) (hmean : (∑ x : K, z x) = 0) :
    (∑ x : K, ∑ t ∈ T, z (x * t)) = 0 := by
  rw [Finset.sum_comm]
  simp_rw [regular_sum, hmean]
  simp

private theorem numerical_complex {K : Type*} [Group K] [Fintype K]
    (T : Finset K) (η : ℝ) (hgap : NumericalGap T η)
    (lam : ℂ) (z : K → ℂ) (hmean : (∑ x : K, z x) = 0) (hz : z ≠ 0)
    (heigen : ∀ x : K, (∑ t ∈ T, z (x * t)) = lam * z x) :
    lam.re ≤ (1 - η) * (T.card : ℝ) := by
  let u : K → ℝ := fun x => (z x).re
  let v : K → ℝ := fun x => (z x).im
  have humean : (∑ x : K, u x) = 0 := by
    simpa [u] using congrArg Complex.re hmean
  have hvmean : (∑ x : K, v x) = 0 := by
    simpa [v] using congrArg Complex.im hmean
  have hu := hgap u humean
  have hv := hgap v hvmean
  have hre (x : K) : (∑ t ∈ T, u (x * t)) = lam.re * u x - lam.im * v x := by
    simpa [u, v, Complex.mul_re] using congrArg Complex.re (heigen x)
  have him (x : K) : (∑ t ∈ T, v (x * t)) = lam.re * v x + lam.im * u x := by
    simpa [u, v, Complex.mul_im] using congrArg Complex.im (heigen x)
  have henergy : (∑ x : K, ∑ t ∈ T, u x * u (x * t)) +
        (∑ x : K, ∑ t ∈ T, v x * v (x * t)) =
      lam.re * ((∑ x : K, u x ^ 2) + (∑ x : K, v x ^ 2)) := by
    simp_rw [← Finset.mul_sum, hre, him]
    rw [← Finset.sum_add_distrib]
    simp_rw [show ∀ x : K, u x * (lam.re * u x - lam.im * v x) +
      v x * (lam.re * v x + lam.im * u x) = lam.re * (u x ^ 2 + v x ^ 2) by intro; ring]
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hmass : 0 < (∑ x : K, u x ^ 2) + (∑ x : K, v x ^ 2) := by
    obtain ⟨x, hx⟩ : ∃ x : K, z x ≠ 0 := by
      by_contra! h
      exact hz (funext h)
    have hcoord : 0 < u x ^ 2 + v x ^ 2 := by
      by_contra h
      have hu0 : u x = 0 := by nlinarith [sq_nonneg (u x), sq_nonneg (v x)]
      have hv0 : v x = 0 := by nlinarith [sq_nonneg (u x), sq_nonneg (v x)]
      exact hx (Complex.ext hu0 hv0)
    have hle : u x ^ 2 + v x ^ 2 ≤ ∑ y : K, (u y ^ 2 + v y ^ 2) :=
      Finset.single_le_sum (fun y _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) (Finset.mem_univ x)
    rw [Finset.sum_add_distrib] at hle
    linarith
  have hbound : lam.re * ((∑ x : K, u x ^ 2) + (∑ x : K, v x ^ 2)) ≤
      ((1 - η) * (T.card : ℝ)) * ((∑ x : K, u x ^ 2) + (∑ x : K, v x ^ 2)) := by
    rw [← henergy]
    nlinarith
  exact (mul_le_mul_iff_left₀ hmass).mp hbound

private theorem original_colour_coset {G : Type*} [Group G] [Fintype G]
    (S : Finset G) (H : Subgroup G) (a : G) :
    Function.Bijective (leftCosetMap H a) ∧
      (∀ (h k : H) (s : G),
        (s ∈ S ∧ (leftCosetMap H a k : G) = (leftCosetMap H a h : G) * s) ↔
          ∃ t ∈ retained S H, (t : G) = s ∧ k = h * t) := by
  constructor
  · constructor
    · intro h k he
      apply Subtype.ext
      exact mul_left_cancel (congrArg Subtype.val he)
    · intro x
      refine ⟨⟨a⁻¹ * x.val, x.property⟩, ?_⟩
      apply Subtype.ext
      simp [leftCosetMap, mul_assoc]
  · intro h k s
    constructor
    · rintro ⟨hs, he⟩
      have hk : (k : G) = (h : G) * s := by
        apply mul_left_cancel (a := a)
        simpa only [leftCosetMap, mul_assoc] using he
      let t : H := h⁻¹ * k
      have ht : (t : G) = s := by
        change (h : G)⁻¹ * (k : G) = s
        rw [hk]
        simp [mul_assoc]
      refine ⟨t, (retained_mem S H t).mpr (by simpa only [ht] using hs), ht, ?_⟩
      dsimp [t]
      simp [mul_assoc]
    · rintro ⟨t, ht, rfl, rfl⟩
      refine ⟨(retained_mem S H t).mp ht, ?_⟩
      simp [leftCosetMap, mul_assoc]

private theorem retained_index {G : Type*} [Group G] [Fintype G]
    (S : Finset G) (hS : S.Nonempty) (ε : ℝ) (hεhalf : ε < (1 / 2 : ℝ))
    (H : Subgroup G) (hret : (1 - ε) * (S.card : ℝ) ≤ (retained S H).card) :
    (H.index : ℝ) ≤ 1 / ((1 - ε) * density S) ∧
      1 / ((1 - ε) * density S) < 2 / density S ∧ (H.index : ℝ) < 2 / density S := by
  have hσ : 0 < density S := density_pos S hS
  have he : 0 < 1 - ε := by linarith
  have hden : 0 < (1 - ε) * density S := mul_pos he hσ
  have hcard : (Fintype.card H : ℝ) * H.index = Fintype.card G := by
    have hnat : Fintype.card H * H.index = Fintype.card G := by
      simpa only [Nat.card_eq_fintype_card] using H.card_mul_index
    exact_mod_cast hnat
  have hupper : ((retained S H).card : ℝ) ≤ Fintype.card H := by
    exact_mod_cast (retained S H).card_le_univ
  have hbound := mul_le_mul_of_nonneg_right (le_trans hret hupper) (show (0 : ℝ) ≤ H.index by positivity)
  have hg : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hσg : density S * Fintype.card G = S.card := div_mul_cancel₀ _ hg.ne'
  have hi : (H.index : ℝ) ≤ 1 / ((1 - ε) * density S) := by
    apply (le_div_iff₀ hden).mpr
    rw [hcard] at hbound
    rw [← hσg] at hbound
    apply (mul_le_mul_iff_left₀ hg).mp
    convert hbound using 1 <;> ring
  have hrecip : 1 / ((1 - ε) * density S) < 2 / density S := by
    apply (div_lt_div_iff₀ hden hσ).mpr
    have hstrict := mul_pos (show 0 < 1 - 2 * ε by linarith) hσ
    nlinarith
  exact ⟨hi, hrecip, lt_of_le_of_lt hi hrecip⟩

/-- Full original-label Cayley concentration. The subgroup is constructed by
well-founded cardinal descent from a failed numerical inequality. The directed
cut, complex restriction, original-colour coset and strict index conclusions
are consequences, with no gap, localizer or stage certificate as a premise.
Adapted from Bedert–Bucić–Kravitz–Montgomery–Müyesser, Section 4; no novelty claim. -/
theorem exists_subgroup_concentration
    {G : Type*} [Group G] [Fintype G]
    (S : Finset G) (hS : S.Nonempty)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < (1 / 2 : ℝ)) :
    ∃ H : Subgroup G,
      let T := retained S H
      let σ := density S
      let τ := density T
      let η := ε * σ ^ 2 / 1000
      (1 - ε) * (S.card : ℝ) ≤ (T.card : ℝ) ∧
      σ ≤ τ ∧ NumericalGap T η ∧
      (∀ X Y : Finset H, Disjoint X Y → X ∪ Y = Finset.univ →
        η * τ * (X.card : ℝ) * (Y.card : ℝ) ≤ (directedCut T X Y : ℝ) ∧
        (ε * σ ^ 3 / 1000) * (X.card : ℝ) * (Y.card : ℝ) ≤
          η * τ * (X.card : ℝ) * (Y.card : ℝ) ∧
        directedCut T X Y = directedCut T Y X) ∧
      (∀ z : H → ℂ, (∑ x : H, z x) = 0 →
        (∑ x : H, ∑ t ∈ T, z (x * t)) = 0) ∧
      (∀ (lam : ℂ) (z : H → ℂ),
        (∑ x : H, z x) = 0 → z ≠ 0 →
        (∀ x : H, (∑ t ∈ T, z (x * t)) = lam * z x) →
        lam.re ≤ (1 - η) * (T.card : ℝ)) ∧
      (∀ a : G,
        Function.Bijective (leftCosetMap H a) ∧
        (∀ (h k : H) (s : G),
          (s ∈ S ∧ (leftCosetMap H a k : G) = (leftCosetMap H a h : G) * s) ↔
            ∃ t ∈ T, (t : G) = s ∧ k = h * t)) ∧
      ((H.index : ℝ) ≤ 1 / ((1 - ε) * σ) ∧
        1 / ((1 - ε) * σ) < 2 / σ ∧ (H.index : ℝ) < 2 / σ) := by
  obtain ⟨H, hretain, hdense, hgap⟩ := numerical_descent S hS ε hε hεhalf
  refine ⟨H, hretain, hdense, hgap, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y hdisj hcover
    obtain ⟨hcut, hbalance⟩ := numerical_cut _ _ hgap X Y hdisj
      (by simpa only [Finset.ext_iff, Finset.mem_union, Finset.mem_univ] using hcover)
    refine ⟨hcut, ?_, hbalance⟩
    have hσ := density_pos S hS
    have hbase : ε * density S ^ 3 / 1000 ≤
        (ε * density S ^ 2 / 1000) * density (retained S H) := by
      have := mul_le_mul_of_nonneg_left hdense
        (show 0 ≤ ε * density S ^ 2 / 1000 by positivity)
      nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbase (by positivity)) (by positivity)
  · exact adjacency_mean_zero _
  · exact numerical_complex _ _ hgap
  · exact original_colour_coset S H
  · exact retained_index S hS ε hεhalf H hretain

end
end D5.S3.Combinatorics.Sequenceability.CayleyNumericalConcentration
