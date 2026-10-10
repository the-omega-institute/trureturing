/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/EffectiveRationalTransportTail
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/EffectiveRationalTransportTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual historical survivor transport and an executable rational certificate. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HistoricalDepthBudgetJointExtremum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

open scoped BigOperators ENNReal
open Finset MeasureTheory
open D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HistoricalDepthBudgetJointExtremum

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.EffectiveRationalTransportTail

set_option maxRecDepth 4000
set_option maxHeartbeats 2000000 in
/-- A finite surviving clopen transports between actual normalized historical laws;
the remaining error is bounded under the second original law, without absolute continuity
of the two infinite laws or a supplied positive survivor gap. -/
theorem historical_survivor_transport {A : Type*} [Fintype A] [DecidableEq A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (a₀ : A) (δ : ℝ) (hδ : 0 < δ) (hd : 2 ≤ Fintype.card A)
    (hδmax : δ ≤ 1 / (Fintype.card A : ℝ))
    (q₀ q₁ : List A → A → ℝ) (hq₀ : NormalizedRows q₀) (hq₁ : NormalizedRows q₁)
    (hlo : ∀ v z, δ ≤ q₁ v z)
    (c : ℝ) (hc : 0 ≤ c) (hrow : ∀ v z, q₀ v z ≤ c * q₁ v z)
    (b : ℕ → ℕ) (F : Set (List A)) (hF : Legal b F)
    (a : ℝ) (ha : 0 ≤ a) (N : ℕ)
    (hbud : ∀ n, N < n → (b n : ℝ) ≤ a ^ n)
    (hρ : a * (1 - ((Fintype.card A : ℝ) - 1) * δ) < 1) :
    ((trajectoryLaw q₀ hq₀) (deletedSet F)ᶜ).toReal ≤
      c ^ N * ((trajectoryLaw q₁ hq₁) (deletedSet F)ᶜ).toReal +
      (a * (1 - ((Fintype.card A : ℝ) - 1) * δ)) *
        (c * (a * (1 - ((Fintype.card A : ℝ) - 1) * δ))) ^ N /
        (1 - a * (1 - ((Fintype.card A : ℝ) - 1) * δ)) := by
  classical
  letI : Encodable (List A) := Encodable.ofCountable _
  let tie : ℕ → LinearOrder (List A) := fun _ =>
    LinearOrder.lift' Encodable.encode Encodable.encode_injective
  have suppliers := historical_depth_budget_joint_extremum a₀ δ hδ hd hδmax b tie
  have laws := suppliers.2.1
  let μ := trajectoryLaw q₀ hq₀
  let ν := trajectoryLaw q₁ hq₁
  letI : IsProbabilityMeasure μ := (laws q₀ hq₀).1
  letI : IsProbabilityMeasure ν := (laws q₁ hq₁).1
  let r := 1 - ((Fintype.card A : ℝ) - 1) * δ
  let ρ := a * r
  have rowupper (v : List A) (z : A) : q₁ v z ≤ r := by
    have hh := Finset.sum_le_sum (s := Finset.univ.erase z) (fun x _ => hlo v x)
    have hs := hq₁.2 v
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ z)] at hs
    simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ z),
      Finset.card_univ, nsmul_eq_mul] at hh
    have hd0 : 1 ≤ Fintype.card A := by omega
    rw [Nat.cast_sub hd0, Nat.cast_one] at hh
    dsimp [r]; linarith
  have hr : 0 ≤ r := (hq₁.1 [] a₀).trans (rowupper [] a₀)
  have hρ0 : 0 ≤ ρ := mul_nonneg ha hr
  have hρ1 : ρ < 1 := hρ
  have cm (w : List A) : MeasurableSet (wordCylinder w) := by
    have each (i : Fin w.length) : MeasurableSet {x : ℕ → A | x i.1 = w.get i} :=
      (measurableSet_singleton (w.get i)).preimage (measurable_pi_apply i.1)
    convert MeasurableSet.iInter each using 1
    ext x
    simp [wordCylinder]
  have ml (H : Set (List A)) (w : List A) (n : ℕ) :
      w ∈ level H n ↔ w.length = n ∧ w ∈ H := by
    simp only [level, words, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨w,rfl⟩,hw⟩; exact ⟨w.2,hw⟩
    · rintro ⟨hl,hw⟩; exact ⟨⟨⟨w,hl⟩,rfl⟩,hw⟩
  have upperword (w : List A) : ν (wordCylinder w) ≤ ENNReal.ofReal (r ^ w.length) := by
    rw [(laws q₁ hq₁).2 w]
    apply ENNReal.ofReal_le_ofReal
    calc
      (∏ i : Fin w.length, q₁ (w.take i.1) (w.get i)) ≤ ∏ _i : Fin w.length, r :=
        Finset.prod_le_prod (fun i _ => hq₁.1 _ _) (fun i _ => rowupper _ _)
      _ = r ^ w.length := by simp
  have compareword (w : List A) :
      μ (wordCylinder w) ≤ ENNReal.ofReal (c ^ w.length) * ν (wordCylinder w) := by
    rw [(laws q₀ hq₀).2 w, (laws q₁ hq₁).2 w,
      ← ENNReal.ofReal_mul (pow_nonneg hc _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      (∏ i : Fin w.length, q₀ (w.take i.1) (w.get i)) ≤
          ∏ i : Fin w.length, c * q₁ (w.take i.1) (w.get i) :=
        Finset.prod_le_prod (fun i _ => hq₀.1 _ _) (fun i _ => hrow _ _)
      _ = c ^ w.length * ∏ i : Fin w.length, q₁ (w.take i.1) (w.get i) := by
        rw [Finset.prod_mul_distrib]; simp
  let U := deletedSet F
  let UN := deletedSet {w | w ∈ F ∧ w.length ≤ N}
  let L := deletedSet {w | w ∈ F ∧ N < w.length}
  have splitU : U = UN ∪ L := by
    ext x
    simp only [U, UN, L, deletedSet, Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨w,hw,hx⟩
      by_cases hn : w.length ≤ N
      · exact Or.inl ⟨w,⟨hw,hn⟩,hx⟩
      · exact Or.inr ⟨w,⟨hw,by omega⟩,hx⟩
    · rintro (⟨w,⟨hw,_⟩,hx⟩ | ⟨w,⟨hw,_⟩,hx⟩) <;> exact ⟨w,hw,hx⟩
  have ls : L = ⋃ k : ℕ, ⋃ w ∈ level F (N+1+k), wordCylinder w := by
    ext x
    simp only [L, deletedSet, Set.mem_iUnion]
    constructor
    · rintro ⟨w,⟨hw,hn⟩,hx⟩
      exact ⟨w.length-(N+1),w,(ml _ _ _).mpr ⟨by omega,hw⟩,hx⟩
    · rintro ⟨k,w,hw,hx⟩
      obtain ⟨hl,hw⟩ := (ml _ _ _).mp hw
      exact ⟨w,⟨hw,by omega⟩,hx⟩
  have levelbound (k : ℕ) :
      ν (⋃ w ∈ level F (N+1+k), wordCylinder w) ≤ ENNReal.ofReal (ρ ^ (N+1+k)) := by
    calc
      _ ≤ ∑ w ∈ level F (N+1+k), ν (wordCylinder w) := measure_biUnion_finset_le _ _
      _ ≤ ∑ w ∈ level F (N+1+k), ENNReal.ofReal (r ^ (N+1+k)) := by
        apply Finset.sum_le_sum
        intro w hw
        simpa only [((ml _ _ _).mp hw).1] using upperword w
      _ = ENNReal.ofReal ((level F (N+1+k)).card * r ^ (N+1+k)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul,
          Nat.cast_nonneg, ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((b (N+1+k) : ℝ) * r ^ (N+1+k)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hF.2.2 (N+1+k)) (pow_nonneg hr _)
      _ ≤ ENNReal.ofReal (a ^ (N+1+k) * r ^ (N+1+k)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hbud _ (by omega)) (pow_nonneg hr _))
      _ = _ := by rw [← mul_pow]
  have tailsum : (∑' k : ℕ, ENNReal.ofReal (ρ ^ (N+1+k))) =
      ENNReal.ofReal (ρ ^ (N+1) / (1-ρ)) := by
    have hs := (hasSum_geometric_of_lt_one hρ0 hρ1).mul_left (ρ ^ (N+1))
    simp_rw [← pow_add] at hs
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => pow_nonneg hρ0 _) hs.summable,
      hs.tsum_eq, div_eq_mul_inv]
  have tailbound : ν L ≤ ENNReal.ofReal (ρ ^ (N+1) / (1-ρ)) := by
    rw [ls]
    exact (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum levelbound).trans_eq tailsum)
  let H := (words (α := A) N).filter (fun v => ¬ ∃ w ∈ F, w.length ≤ N ∧ w <+: v)
  have hm (v : List A) : v ∈ H ↔ v.length = N ∧ ¬ ∃ w ∈ F, w.length ≤ N ∧ w <+: v := by
    simp only [H, words, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨v,rfl⟩,hh⟩; exact ⟨v.2,hh⟩
    · rintro ⟨hl,hh⟩; exact ⟨⟨⟨v,hl⟩,rfl⟩,hh⟩
  have hcyl : UNᶜ = ⋃ v ∈ H, wordCylinder v := by
    ext x
    simp only [Set.mem_compl_iff, UN, deletedSet, Set.mem_iUnion]
    constructor
    · intro hx
      let v := List.ofFn (fun i : Fin N => x i.1)
      have hv : v.length = N := by simp [v]
      have xv : x ∈ wordCylinder v := by intro i; simp [v, List.get_eq_getElem]
      refine ⟨v,(hm v).mpr ⟨hv,?_⟩,xv⟩
      rintro ⟨w,hw,hn,hp⟩
      apply hx
      refine ⟨w,⟨hw,hn⟩,fun i => ?_⟩
      exact (xv ⟨i.1,i.2.trans_le hp.length_le⟩).trans
        (by simpa only [List.get_eq_getElem] using (hp.getElem i.2).symm)
    · rintro ⟨v,hv,hx⟩ ⟨w,⟨hw,hn⟩,hwx⟩
      obtain ⟨hl,hnot⟩ := (hm v).mp hv
      apply hnot
      refine ⟨w,hw,hn,List.prefix_iff_getElem.mpr ⟨by omega,fun i hi => ?_⟩⟩
      exact (hwx ⟨i,hi⟩).symm.trans (hx ⟨i,by omega⟩)
  have disjointH : (H : Set (List A)).PairwiseDisjoint wordCylinder := by
    intro v hv w hw hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    apply hne
    have hvN := ((hm v).mp hv).1
    have hwN := ((hm w).mp hw).1
    apply List.ext_getElem
    · omega
    · intro i hi hj
      exact (hx ⟨i,hi⟩).symm.trans (hy ⟨i,hj⟩)
  have finitecompare : μ UNᶜ ≤ ENNReal.ofReal (c^N) * ν UNᶜ := by
    rw [hcyl, measure_biUnion_finset disjointH (fun v _ => cm v),
      measure_biUnion_finset disjointH (fun v _ => cm v), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    simpa only [((hm v).mp hv).1] using compareword v
  have ecover : UNᶜ ⊆ Uᶜ ∪ L := by
    rw [splitU]
    intro x hx
    by_cases hl : x ∈ L
    · exact Or.inr hl
    · exact Or.inl (by simp only [Set.mem_compl_iff, Set.mem_union]; tauto)
  have subE : Uᶜ ⊆ UNᶜ := by rw [splitU]; exact Set.compl_subset_compl.mpr Set.subset_union_left
  have tν : ν.real UNᶜ ≤ ν.real Uᶜ + ρ ^ (N+1) / (1-ρ) := by
    have tl : ν.real L ≤ ρ ^ (N+1) / (1-ρ) := by
      have hn : 0 ≤ ρ ^ (N+1) / (1-ρ) :=
        div_nonneg (pow_nonneg hρ0 _) (sub_nonneg.mpr hρ1.le)
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top tailbound).trans_eq (ENNReal.toReal_ofReal hn)
    exact (measureReal_mono ecover).trans ((measureReal_union_le _ _).trans
      (add_le_add_right tl _))
  have fc : μ.real UNᶜ ≤ c^N * ν.real UNᶜ := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν _)) finitecompare
    change (μ UNᶜ).toReal ≤ c^N * (ν UNᶜ).toReal
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hc _)] using hh
  change μ.real Uᶜ ≤ c^N * ν.real Uᶜ + ρ * (c*ρ)^N / (1-ρ)
  calc
    μ.real Uᶜ ≤ μ.real UNᶜ := measureReal_mono subE
    _ ≤ c^N * ν.real UNᶜ := fc
    _ ≤ c^N * (ν.real Uᶜ + ρ ^ (N+1) / (1-ρ)) :=
      mul_le_mul_of_nonneg_left tν (pow_nonneg hc _)
    _ = _ := by rw [pow_succ, mul_pow c ρ]; ring

#print axioms historical_survivor_transport

-- Preserve dependent certificate lets through elaboration; kernel checking remains enabled.
set_option cleanup.letToHave false in
set_option maxHeartbeats 4000000 in
/-- A proof-erased executable rational certificate, uniform over every legal code and
every full-history law with the supplied positive row bound. Its runtime inputs are
the alphabet size, rational bound, budget function and effective modulus. -/
def q_free_historical_rational_certificate
    (d : ℕ) (hd : 2 ≤ d) (δ : ℚ) (hδ : 0 < δ) (hδmax : δ ≤ 1/(d : ℚ))
    (b : ℕ → ℕ) (ν : ℚ → ℕ) (oneWord : Bool)
    (hOneWord : oneWord = true → 3 ≤ d ∧ ∀ n, b n = 1)
    (hν : ∀ t : ℚ, 1 < t → ∀ n, ν t ≤ n → (b n : ℚ) ≤ t ^ n)
    (hB : (∑' n : ℕ, (b (n+1) : ℝ) / (d : ℝ) ^ (n+1)) < 1) :
    letI : MeasurableSpace (Fin d) := ⊤
    letI : MeasurableSingletonClass (Fin d) := ⟨fun _ => trivial⟩
    {γ : ℚ // 0 < γ ∧
      (∀ (q : List (Fin d) → Fin d → ℝ) (hq : NormalizedRows q),
        (∀ v z, (δ : ℝ) ≤ q v z) → ∀ (F : Set (List (Fin d))), Legal b F →
          (γ : ℝ) ≤ ((trajectoryLaw q hq) (deletedSet F)ᶜ).toReal) ∧
      (γ : ℝ) ≤ historicalGap (A := Fin d) (δ : ℝ) b ∧
      (oneWord = true → ∀ (p : Fin d → ℝ), (∀ z, (δ : ℝ) < p z) →
        (∑ z, p z = 1) → (γ : ℝ) < 1 - sSup {x : ℝ | ∃ F : Set (List (Fin d)),
          Legal (fun _ => 1) F ∧ x = (codeMass p F).toReal})} := by
  letI : MeasurableSpace (Fin d) := ⊤
  letI : MeasurableSingletonClass (Fin d) := ⟨fun _ => trivial⟩
  have hdq : (0 : ℚ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd2 : (2 : ℚ) ≤ d := by exact_mod_cast hd
  have hδd : (d : ℚ) * δ ≤ 1 := by
    simpa only [mul_comm] using (le_div_iff₀ hdq).mp hδmax
  let r : ℚ := 1 - ((d : ℚ)-1)*δ
  have hr0 : 0 < r := by dsimp [r]; nlinarith only [hδd,hδ]
  have hr1 : r < 1 := by
    exact sub_lt_self 1 (mul_pos (by linarith only [hd2]) hδ)
  have hdr : 1 ≤ (d : ℚ)*r := by
    have hh := mul_le_mul_of_nonneg_left hδd (by linarith only [hd2] : (0 : ℚ) ≤ d-1)
    dsimp [r]; nlinarith only [hh]
  let basea : ℚ := (1+1/r)/2
  have hbasea : 1 < basea := by
    have hh : 1 < 1/r := (lt_div_iff₀ hr0).mpr (by simpa using hr1)
    dsimp [basea]; linarith only [hh]
  let a : ℚ := if oneWord then 1 else basea
  have ha0 : 1 ≤ a := by cases oneWord <;> simp [a] <;> linarith
  have hagen (h : oneWord = false) : 1 < a := by simpa [a,h] using hbasea
  let ρ : ℚ := a*r
  have hρ0 : 0 < ρ := mul_pos (by linarith only [ha0]) hr0
  have hρ1 : ρ < 1 := by
    cases oneWord with
    | true => simpa [ρ,a] using hr1
    | false =>
      have he : ρ = (1+r)/2 := by dsimp [ρ,a,basea]; field_simp <;> ring
      rw [he]; linarith only [hr1]
  have had : a < d := (mul_lt_mul_iff_left₀ hr0).mp (hρ1.trans_le hdr)
  let c : ℚ := if oneWord then 1+δ else (1+1/ρ)/2
  have hc : 1 < c := by
    cases oneWord with
    | true => dsimp [c]; linarith only [hδ]
    | false =>
      have hh : 1 < 1/ρ := (lt_div_iff₀ hρ0).mpr (by simpa using hρ1)
      dsimp [c]; linarith only [hh]
  have hcρ : c*ρ < 1 := by
    cases oneWord with
    | true =>
      have he : c*ρ = 1-((d : ℚ)-2)*δ-((d : ℚ)-1)*δ^2 := by
        dsimp [c,ρ,a,r]; ring
      rw [he]
      have hh : 0 ≤ ((d : ℚ)-2)*δ := mul_nonneg (by linarith only [hd2]) hδ.le
      have hp : 0 < ((d : ℚ)-1)*δ^2 := mul_pos (by linarith only [hd2]) (pow_pos hδ _)
      linarith only [hh,hp]
    | false =>
      have he : c*ρ = (1+ρ)/2 := by dsimp [c]; field_simp <;> ring
      rw [he]; linarith only [hρ1]
  let J : ℕ := ⌊1/((c-1)*δ)⌋₊ + 1
  have hJ0 : 0 < J := by dsimp [J]; omega
  have hJ : 1 + 1/((J : ℚ)*δ) < c := by
    have hh : 1/((c-1)*δ) < (J : ℚ) := by
      simpa [J] using Nat.lt_floor_add_one (1/((c-1)*δ))
    have hp : 0 < (c-1)*δ := mul_pos (by linarith) hδ
    have hh' := (div_lt_iff₀ hp).mp hh
    have hJq : (0 : ℚ) < J := by exact_mod_cast hJ0
    have hdiv : 1/((J : ℚ)*δ) < c-1 :=
      (div_lt_iff₀ (mul_pos hJq hδ)).mpr (by nlinarith)
    linarith
  let initial : {γ : ℚ // 0 < γ ∧
      (γ : ℝ) ≤ 1 - ∑' n : ℕ, (b (n+1) : ℝ) / (d : ℝ) ^ (n+1)} := by
    by_cases ho : oneWord = true
    · have hd3 : (3 : ℚ) ≤ d := by exact_mod_cast (hOneWord ho).1
      have hd3r : (3 : ℝ) ≤ d := by exact_mod_cast (hOneWord ho).1
      refine ⟨((d : ℚ)-2)/((d : ℚ)-1),
        div_pos (by linarith only [hd3]) (by linarith only [hd3]),?_⟩
      have hdr0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have ht0 : (0 : ℝ) ≤ 1/(d : ℝ) := by positivity
      have ht1 : 1/(d : ℝ) < 1 := (div_lt_one hdr0).mpr (by linarith only [hd3r])
      have hs := (hasSum_geometric_of_lt_one ht0 ht1).mul_left (1/(d : ℝ))
      have he : (∑' n : ℕ, (b (n+1) : ℝ)/(d : ℝ)^(n+1)) = 1/((d : ℝ)-1) := by
        have hf : (fun n : ℕ => (b (n+1) : ℝ)/(d : ℝ)^(n+1)) =
            (fun n : ℕ => (1/(d : ℝ)) * (1/(d : ℝ))^n) := by
          funext n
          simp only [(hOneWord ho).2, Nat.cast_one, one_div_pow, pow_succ]
          field_simp <;> ring
        rw [hf,hs.tsum_eq]
        field_simp <;> ring
      rw [he]
      push_cast
      have hd1 : (d : ℝ)-1 ≠ 0 := by linarith only [hd3r]
      exact le_of_eq (by field_simp; ring)
    · have hf : oneWord = false := Bool.eq_false_iff.mpr ho
      have ha : 1 < a := hagen hf
      let searched :
          {z : ℕ × ℚ // ν a ≤ z.1 ∧
            z.2 = 1 - ((∑ n ∈ Finset.range z.1, (b (n+1) : ℚ) / (d : ℚ) ^ (n+1)) +
              (a / d) ^ (z.1+1) / (1-a/d)) ∧ 0 < z.2 ∧
            (z.2 : ℝ) ≤ 1 - ∑' n : ℕ, (b (n+1) : ℝ) / (d : ℝ) ^ (n+1)} := by
        have hdq : (0 : ℚ) < d := by exact_mod_cast (by omega : 0 < d)
        have hdr : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
        let t : ℚ := a/d
        have ht0 : 0 ≤ t := div_nonneg (by linarith) hdq.le
        have ht1 : t < 1 := by dsimp [t]; exact (div_lt_one hdq).mpr had
        let U : ℕ → ℚ := fun N =>
          (∑ n ∈ Finset.range N, (b (n+1) : ℚ) / (d : ℚ) ^ (n+1)) +
            t ^ (N+1) / (1-t)
        have analysis : (∃ N : ℕ, ν a ≤ N ∧ U N < 1) ∧
            (∀ N : ℕ, ν a ≤ N →
              (∑' n : ℕ, (b (n+1) : ℝ) / (d : ℝ) ^ (n+1)) ≤ (U N : ℝ)) := by
          let f : ℕ → ℝ := fun n => (b (n+1) : ℝ) / (d : ℝ) ^ (n+1)
          have fpos (n : ℕ) : 0 ≤ f n := by dsimp [f]; positivity
          have tr0 : (0 : ℝ) ≤ t := by exact_mod_cast ht0
          have tr1 : (t : ℝ) < 1 := by exact_mod_cast ht1
          have gsum : Summable (fun n : ℕ => (t : ℝ) ^ (n+1)) := by
            simpa only [pow_succ, mul_comm] using
              (summable_geometric_of_lt_one tr0 tr1).mul_left (t : ℝ)
          have fs : Summable f := by
            apply gsum.of_norm_bounded_eventually_nat
            filter_upwards [Filter.eventually_ge_atTop (ν a)] with n hn
            rw [Real.norm_eq_abs, abs_of_nonneg (fpos n)]
            have hb : (b (n+1) : ℝ) ≤ (a : ℝ) ^ (n+1) := by
              exact_mod_cast hν a ha (n+1) (by omega)
            dsimp [f,t]
            push_cast
            rw [div_pow]
            exact div_le_div_of_nonneg_right hb (pow_nonneg hdr.le _)
          have conv : Filter.Tendsto (fun N => (U N : ℝ)) Filter.atTop
              (nhds (∑' n, f n)) := by
            have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one tr0 tr1).comp
              (Filter.tendsto_add_atTop_nat 1)
            have ht := hp.div_const (1-(t : ℝ))
            have hs := fs.hasSum.tendsto_sum_nat
            convert hs.add ht using 1 <;> simp [U,f]
          have term : ∃ N : ℕ, ν a ≤ N ∧ U N < 1 := by
            have hlim : (∑' n, f n) < 1 := hB
            have he := conv.eventually_lt_const hlim
            have hn := Filter.eventually_ge_atTop (ν a)
            obtain ⟨N,hN,hlt⟩ := (hn.and he).exists
            exact ⟨N,hN,by exact_mod_cast hlt⟩
          refine ⟨term,?_⟩
          intro N hN
          have hgeom := (hasSum_geometric_of_lt_one tr0 tr1).mul_left ((t : ℝ) ^ (N+1))
          have htail : Summable (fun k : ℕ => f (k+N)) :=
            (summable_nat_add_iff N).mpr fs
          have hb (k : ℕ) : f (k+N) ≤ (t : ℝ) ^ (N+1+k) := by
            have hb : (b (k+N+1) : ℝ) ≤ (a : ℝ) ^ (k+N+1) := by
              exact_mod_cast hν a ha (k+N+1) (by omega)
            dsimp [f,t]
            push_cast
            rw [div_pow]
            convert div_le_div_of_nonneg_right hb (pow_nonneg hdr.le _) using 1 <;>
              congr 2 <;> omega
          have hg : Summable (fun k : ℕ => (t : ℝ) ^ (N+1+k)) := by
            simpa only [pow_add] using hgeom.summable
          have ht := htail.tsum_le_tsum hb hg
          have ge : (∑' k : ℕ, (t : ℝ) ^ (N+1+k)) = (t : ℝ) ^ (N+1)/(1-(t : ℝ)) := by
            simpa only [pow_add, div_eq_mul_inv] using hgeom.tsum_eq
          rw [ge] at ht
          have he := fs.sum_add_tsum_nat_add N
          rw [← he]
          simpa [U,f] using add_le_add_left ht (∑ n ∈ Finset.range N, f n)
        let N := Nat.find analysis.1
        have spec : ν a ≤ N ∧ U N < 1 := Nat.find_spec analysis.1
        refine ⟨(N,1-U N),spec.1,rfl,sub_pos.mpr spec.2,?_⟩
        push_cast
        exact sub_le_sub_left (analysis.2 N spec.1) 1
      exact ⟨searched.1.2,searched.2.2.2.1,searched.2.2.2.2⟩
  let start : {γ : ℚ // 0 < γ} := ⟨initial.1,initial.2.1⟩
  let cutoff : ℕ := if oneWord then 1 else max 1 (ν a)
  have budgetBound (n : ℕ) (hn : cutoff ≤ n) : (b n : ℝ) ≤ (a : ℝ)^n := by
    by_cases ho : oneWord = true
    · simp [(hOneWord ho).2,a,ho]
    · have hf : oneWord = false := Bool.eq_false_iff.mpr ho
      have hh : max 1 (ν a) ≤ n := by simpa [cutoff,hf] using hn
      exact_mod_cast hν a (hagen hf) n (Nat.le_trans (Nat.le_max_right _ _) hh)
  have term (γ : {x : ℚ // 0 < x}) :
      ∃ N : ℕ, cutoff ≤ N ∧ ρ*(c*ρ)^N/(1-ρ) < γ.1/2 := by
    have he : 0 < γ.1*(1-ρ)/(2*ρ) :=
      div_pos (mul_pos γ.2 (sub_pos.mpr hρ1)) (mul_pos (by norm_num) hρ0)
    obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one he hcρ
    let N := max cutoff n
    have hp : (c*ρ)^N < γ.1*(1-ρ)/(2*ρ) :=
      (pow_le_pow_of_le_one (by positivity) hcρ.le (Nat.le_max_right _ _)).trans_lt hn
    refine ⟨N,Nat.le_max_left _ _,?_⟩
    have hm := mul_lt_mul_of_pos_left hp hρ0
    have heq : ρ * (γ.1*(1-ρ)/(2*ρ)) = (γ.1/2)*(1-ρ) := by
      field_simp <;> ring
    rw [heq] at hm
    exact (div_lt_iff₀ (by linarith : 0 < 1-ρ)).mpr hm
  let depth (γ : {x : ℚ // 0 < x}) : ℕ := Nat.find (term γ)
  let step (γ : {x : ℚ // 0 < x}) : {x : ℚ // 0 < x} :=
    ⟨γ.1/(2*c^(depth γ)),div_pos γ.2
      (mul_pos (by norm_num) (pow_pos (by linarith only [hc]) _))⟩
  let gammas : ℕ → {x : ℚ // 0 < x} := Nat.rec start (fun _ γ => step γ)
  have positive : 0 < (gammas J).1 := (gammas J).2
  have universal : ∀ (q : List (Fin d) → Fin d → ℝ) (hq : NormalizedRows q),
      (∀ v z, (δ : ℝ) ≤ q v z) → ∀ (F : Set (List (Fin d))), Legal b F →
      ((gammas J).1 : ℝ) ≤ ((trajectoryLaw q hq) (deletedSet F)ᶜ).toReal := by
    classical
    intro q hq hlo F hF
    have hdr0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
    have hδmr : (δ : ℝ) ≤ 1/(d : ℝ) := by
      have hh : (δ : ℝ) ≤ ((1/(d : ℚ) : ℚ) : ℝ) := by exact_mod_cast hδmax
      simpa using hh
    have hcr : (0 : ℝ) < c := by exact_mod_cast (by linarith : (0 : ℚ) < c)
    have hJr : (0 : ℝ) < J := by exact_mod_cast hJ0
    let a₀ : Fin d := ⟨0,by omega⟩
    letI : Encodable (List (Fin d)) := Encodable.ofCountable _
    let tie : ℕ → LinearOrder (List (Fin d)) := fun _ =>
      LinearOrder.lift' Encodable.encode Encodable.encode_injective
    have suppliers := historical_depth_budget_joint_extremum a₀ (δ : ℝ) hδr
      (by simpa using hd) (by simpa using hδmr) b tie
    have laws := suppliers.2.1
    let Q (j : ℕ) (v : List (Fin d)) (z : Fin d) : ℝ :=
      (1-(j : ℝ)/J)/(d : ℝ) + ((j : ℝ)/J)*q v z
    have hQ (j : ℕ) (hj : j ≤ J) : NormalizedRows (Q j) := by
      have ht : (j : ℝ)/J ≤ 1 := (div_le_one hJr).mpr (by exact_mod_cast hj)
      have ht0 : 0 ≤ (j : ℝ)/J := by positivity
      constructor
      · intro v z
        exact add_nonneg (div_nonneg (by linarith) hdr0.le)
          (mul_nonneg ht0 (hq.1 v z))
      · intro v
        dsimp [Q]
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hq.2 v]
        field_simp <;> ring
    have lowerQ (j : ℕ) (hj : j ≤ J) (v : List (Fin d)) (z : Fin d) :
        (δ : ℝ) ≤ Q j v z := by
      have ht : (j : ℝ)/J ≤ 1 := (div_le_one hJr).mpr (by exact_mod_cast hj)
      have ht0 : 0 ≤ (j : ℝ)/J := by positivity
      have hh := mul_le_mul_of_nonneg_left (hlo v z) ht0
      have hu := mul_le_mul_of_nonneg_left hδmr (sub_nonneg.mpr ht)
      dsimp [Q]
      simp only [div_eq_mul_inv] at hh hu ⊢
      nlinarith only [hh,hu]
    have ratio (j : ℕ) (hj : j+1 ≤ J) (v : List (Fin d)) (z : Fin d) :
        Q j v z ≤ (c : ℝ)*Q (j+1) v z := by
      have hu : 0 ≤ 1/(d : ℝ) := by positivity
      have hqu : q v z ≤ 1 := by
        have hh := Finset.single_le_sum (s := Finset.univ) (f := q v)
          (fun x _ => hq.1 v x) (Finset.mem_univ z)
        simpa only [hq.2 v] using hh
      have hdiff : Q j v z - Q (j+1) v z = ((1/(d : ℝ))-q v z)/(J : ℝ) := by
        dsimp [Q]; push_cast; ring
      have hdif : Q j v z - Q (j+1) v z ≤ 1/(J : ℝ) := by
        rw [hdiff]
        have hud : 1/(d : ℝ) ≤ 1 := (div_le_one hdr0).mpr (by exact_mod_cast (by omega : 1 ≤ d))
        exact div_le_div_of_nonneg_right (by linarith [hq.1 v z]) hJr.le
      have hJc : 1+1/((J : ℝ)*(δ : ℝ)) < (c : ℝ) := by exact_mod_cast hJ
      have he : 1/(J : ℝ) < ((c : ℝ)-1)*(δ : ℝ) := by
        have hh := (div_lt_iff₀ (mul_pos hJr hδr)).mp (by linarith :
          1/((J : ℝ)*(δ : ℝ)) < (c : ℝ)-1)
        apply (div_lt_iff₀ hJr).mpr
        nlinarith only [hh]
      have hl := mul_le_mul_of_nonneg_left (lowerQ (j+1) hj v z)
        (by have hcc : (1 : ℝ) < c := by exact_mod_cast hc
            linarith only [hcc] : (0 : ℝ) ≤ (c : ℝ)-1)
      linarith only [hl,hdif,he]
    have zeroQ : Q 0 = (fun _ _ => 1/(d : ℝ)) := by funext v z; simp [Q]
    have lastQ : Q J = q := by funext v z; simp [Q,ne_of_gt hJr]
    let μ₀ := trajectoryLaw (Q 0) (hQ 0 (by omega))
    letI : IsProbabilityMeasure μ₀ := (laws _ (hQ 0 (by omega))).1
    have initialBound : (start.1 : ℝ) ≤ (μ₀ (deletedSet F)ᶜ).toReal := by
      let f : ℕ → ℝ := fun n => (b (n+1) : ℝ)/(d : ℝ)^(n+1)
      have tr0 : (0 : ℝ) ≤ a/d := by positivity
      have tr1 : (a : ℝ)/d < 1 := (div_lt_one hdr0).mpr (by exact_mod_cast had)
      have gs : Summable (fun n : ℕ => ((a : ℝ)/d)^(n+1)) := by
        simpa only [pow_succ,mul_comm] using
          (summable_geometric_of_lt_one tr0 tr1).mul_left ((a : ℝ)/d)
      have fs : Summable f := by
        apply gs.of_norm_bounded_eventually_nat
        filter_upwards [Filter.eventually_ge_atTop cutoff] with n hn
        have hb : (b (n+1) : ℝ) ≤ (a : ℝ)^(n+1) := by
          exact budgetBound (n+1) (by omega)
        dsimp [f]
        rw [abs_of_nonneg (by positivity), div_pow]
        exact div_le_div_of_nonneg_right hb (by positivity)
      have ml (w : List (Fin d)) (n : ℕ) : w ∈ level F n ↔ w.length = n ∧ w ∈ F := by
        simp only [level,words,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
        constructor
        · rintro ⟨⟨w,rfl⟩,hw⟩; exact ⟨w.2,hw⟩
        · rintro ⟨hl,hw⟩; exact ⟨⟨⟨w,hl⟩,rfl⟩,hw⟩
      have levels : deletedSet F = ⋃ n : ℕ, ⋃ w ∈ level F (n+1), wordCylinder w := by
        ext x
        simp only [deletedSet,Set.mem_iUnion]
        constructor
        · rintro ⟨w,hw,hx⟩
          have hn : 0 < w.length := by
            by_contra he
            have hz : w = [] := List.length_eq_zero_iff.mp (by omega)
            exact hF.2.1 (hz ▸ hw)
          exact ⟨w.length-1,w,(ml _ _).mpr ⟨by omega,hw⟩,hx⟩
        · rintro ⟨n,w,hw,hx⟩; exact ⟨w,((ml _ _).mp hw).2,hx⟩
      have lw (w : List (Fin d)) : μ₀ (wordCylinder w) =
          ENNReal.ofReal (1/(d : ℝ)^w.length) := by
        rw [(laws _ (hQ 0 (by omega))).2 w]
        simp only [zeroQ,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
        simp [one_div_pow]
      have lb (n : ℕ) : μ₀ (⋃ w ∈ level F (n+1), wordCylinder w) ≤ ENNReal.ofReal (f n) := by
        calc
          _ ≤ ∑ w ∈ level F (n+1), μ₀ (wordCylinder w) := measure_biUnion_finset_le _ _
          _ = ENNReal.ofReal ((level F (n+1)).card/(d : ℝ)^(n+1)) := by
            simp_rw [lw]
            have he (w : List (Fin d)) (hw : w ∈ level F (n+1)) : w.length = n+1 := ((ml _ _).mp hw).1
            rw [Finset.sum_congr rfl (fun w hw => congrArg ENNReal.ofReal (by rw [he w hw]))]
            simp [ENNReal.ofReal_div_of_pos, pow_pos hdr0, div_eq_mul_inv]
          _ ≤ _ := ENNReal.ofReal_le_ofReal
            (div_le_div_of_nonneg_right (by exact_mod_cast hF.2.2 (n+1)) (by positivity))
      have ub : μ₀ (deletedSet F) ≤ ENNReal.ofReal (∑' n, f n) := by
        rw [levels]
        exact (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum lb).trans_eq
          (ENNReal.ofReal_tsum_of_nonneg (fun n => by dsimp [f]; positivity) fs).symm)
      have ur : μ₀.real (deletedSet F) ≤ ∑' n, f n := by
        have hb0 : 0 ≤ ∑' n, f n := tsum_nonneg (fun n => by dsimp [f]; positivity)
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top ub).trans_eq
          (ENNReal.toReal_ofReal hb0)
      have cm (w : List (Fin d)) : MeasurableSet (wordCylinder w) := by
        have he (i : Fin w.length) : MeasurableSet {x : ℕ → Fin d | x i.1 = w.get i} :=
          (measurableSet_singleton _).preimage (measurable_pi_apply _)
        convert MeasurableSet.iInter he using 1
        ext x; simp [wordCylinder]
      have um : MeasurableSet (deletedSet F) := MeasurableSet.iUnion (fun w =>
        MeasurableSet.iUnion (fun _ => cm w))
      have comp := measureReal_add_measureReal_compl (μ := μ₀) um
      have total : μ₀.real Set.univ = 1 := by simp [Measure.real]
      rw [total] at comp
      have hi := initial.2.2
      change (start.1 : ℝ) ≤ 1-∑' n, f n at hi
      change (start.1 : ℝ) ≤ μ₀.real (deletedSet F)ᶜ
      linarith
    have inductionBound : ∀ j, (hj : j ≤ J) →
        ((gammas j).1 : ℝ) ≤ ((trajectoryLaw (Q j) (hQ j hj)) (deletedSet F)ᶜ).toReal := by
      intro j
      induction j with
      | zero => intro hj; exact initialBound
      | succ j ih =>
        intro hj
        let N := depth (gammas j)
        have spec : cutoff ≤ N ∧ ρ*(c*ρ)^N/(1-ρ) < (gammas j).1/2 :=
          Nat.find_spec (term (gammas j))
        have hb (n : ℕ) (hn : N < n) : (b n : ℝ) ≤ (a : ℝ)^n := by
          exact budgetBound n (by have := spec.1; omega)
        have transport := historical_survivor_transport a₀ (δ : ℝ) hδr (by simpa using hd)
          (by simpa using hδmr) (Q j) (Q (j+1)) (hQ j (by omega)) (hQ (j+1) hj)
          (lowerQ (j+1) hj) (c : ℝ) hcr.le (ratio j hj) b F hF (a : ℝ)
          (by exact_mod_cast (by linarith only [ha0] : (0 : ℚ) ≤ a)) N hb
          (by simpa [r,ρ] using (show (ρ : ℝ) < 1 by exact_mod_cast hρ1))
        have ht : ((ρ*(c*ρ)^N/(1-ρ) : ℚ) : ℝ) < ((gammas j).1 : ℝ)/2 := by
          exact_mod_cast spec.2
        have old := ih (by omega)
        change (((gammas j).1/(2*c^N) : ℚ) : ℝ) ≤
          ((trajectoryLaw (Q (j+1)) (hQ (j+1) hj)) (deletedSet F)ᶜ).toReal
        push_cast
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*(c : ℝ)^N)).mpr
        have te : (a : ℝ)*(1-((Fintype.card (Fin d) : ℝ)-1)*(δ : ℝ)) = (ρ : ℝ) := by
          simp [ρ,r]
        rw [te] at transport
        push_cast at ht
        nlinarith only [transport,ht,old]
    simpa only [lastQ] using inductionBound J le_rfl
  let output : ℚ := if oneWord then (gammas J).1/2 else (gammas J).1
  have outpos : 0 < output := by cases oneWord <;> simp [output] <;> positivity
  have outle : output ≤ (gammas J).1 := by cases oneWord <;> simp [output] <;> linarith
  have outstrict (ho : oneWord = true) : output < (gammas J).1 := by
    simp only [output,ho,Bool.true_eq,ite_true]; linarith only [positive]
  have universalOut : ∀ (q : List (Fin d) → Fin d → ℝ) (hq : NormalizedRows q),
      (∀ v z, (δ : ℝ) ≤ q v z) → ∀ (F : Set (List (Fin d))), Legal b F →
      (output : ℝ) ≤ ((trajectoryLaw q hq) (deletedSet F)ᶜ).toReal := by
    intro q hq hlo F hF
    exact (show (output : ℝ) ≤ (gammas J).1 by exact_mod_cast outle).trans
      (universal q hq hlo F hF)
  refine ⟨output,outpos,universalOut,?_,?_⟩
  ·
    classical
    have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
    have hδmr : (δ : ℝ) ≤ 1/(d : ℝ) := by
      have hh : (δ : ℝ) ≤ ((1/(d : ℚ) : ℚ) : ℝ) := by exact_mod_cast hδmax
      simpa using hh
    let a₀ : Fin d := ⟨0,by omega⟩
    letI : Encodable (List (Fin d)) := Encodable.ofCountable _
    let tie : ℕ → LinearOrder (List (Fin d)) := fun _ =>
      LinearOrder.lift' Encodable.encode Encodable.encode_injective
    have suppliers := historical_depth_budget_joint_extremum a₀ (δ : ℝ) hδr
      (by simpa using hd) (by simpa using hδmr) b tie
    obtain ⟨hiid,hloiid,_,htotal,_,_,hgap⟩ := suppliers.2.2.2
    let p := extremalVector (δ : ℝ) a₀
    let G := greedyCode (fun n => priority p (tie n)) b
    let μ := trajectoryLaw (fun _ : List (Fin d) => p) hiid
    letI : IsProbabilityMeasure μ := (suppliers.2.1 _ hiid).1
    have bound := universal (fun _ => p) hiid hloiid G suppliers.1
    have cm (w : List (Fin d)) : MeasurableSet (wordCylinder w) := by
      have he (i : Fin w.length) : MeasurableSet {x : ℕ → Fin d | x i.1 = w.get i} :=
        (measurableSet_singleton _).preimage (measurable_pi_apply _)
      convert MeasurableSet.iInter he using 1
      ext x; simp [wordCylinder]
    have um : MeasurableSet (deletedSet G) := MeasurableSet.iUnion (fun w =>
      MeasurableSet.iUnion (fun _ => cm w))
    have comp := measureReal_add_measureReal_compl (μ := μ) um
    have total : μ.real Set.univ = 1 := by simp [Measure.real]
    rw [total] at comp
    rw [hgap]
    change (output : ℝ) ≤ 1-(codeMass p G).toReal
    have small : (output : ℝ) ≤ (gammas J).1 := by exact_mod_cast outle
    have he : μ.real (deletedSet G) = (codeMass p G).toReal := congrArg ENNReal.toReal htotal
    change ((gammas J).1 : ℝ) ≤ μ.real (deletedSet G)ᶜ at bound
    linarith only [bound,he,comp,small]
  · intro ho p hp hsum
    classical
    have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
    let hiid : NormalizedRows (fun _ : List (Fin d) => p) :=
      ⟨fun _ z => (hδr.trans (hp z)).le, fun _ => hsum⟩
    let μ := trajectoryLaw (fun _ : List (Fin d) => p) hiid
    let a₀ : Fin d := ⟨0,by omega⟩
    letI : Encodable (List (Fin d)) := Encodable.ofCountable _
    let tie : ℕ → LinearOrder (List (Fin d)) := fun _ =>
      LinearOrder.lift' Encodable.encode Encodable.encode_injective
    have hδmr : (δ : ℝ) ≤ 1/(d : ℝ) := by
      have hh : (δ : ℝ) ≤ ((1/(d : ℚ) : ℚ) : ℝ) := by exact_mod_cast hδmax
      simpa using hh
    have laws := (historical_depth_budget_joint_extremum a₀ (δ : ℝ) hδr
      (by simpa using hd) (by simpa using hδmr) b tie).2.1
    letI : IsProbabilityMeasure μ := (laws _ hiid).1
    let G := greedyCode (fun n => priority p (tie n)) (fun _ => 1)
    have optimizer := depth_budget_iid_greedy_optimality p (fun z => hδr.trans (hp z))
      hsum (fun _ => 1) tie
    have legalG : Legal (fun _ => 1) G := optimizer.1
    have legalGb : Legal b G := by
      have eb : b = (fun _ => 1) := funext (hOneWord ho).2
      rw [eb]; exact legalG
    have bound := universal (fun _ => p) hiid (fun _ z => (hp z).le) G legalGb
    have cm (w : List (Fin d)) : MeasurableSet (wordCylinder w) := by
      have he (i : Fin w.length) : MeasurableSet {x : ℕ → Fin d | x i.1 = w.get i} :=
        (measurableSet_singleton _).preimage (measurable_pi_apply _)
      convert MeasurableSet.iInter he using 1
      ext x; simp [wordCylinder]
    have disj : Pairwise (fun v w : G => Disjoint (wordCylinder v.1) (wordCylinder w.1)) := by
      intro v w hne
      apply Set.disjoint_left.mpr
      intro x hv hw
      have pref : v.1 <+: w.1 ∨ w.1 <+: v.1 := by
        by_cases hh : v.1.length ≤ w.1.length
        · left
          apply List.prefix_iff_getElem.mpr
          refine ⟨hh,fun i hi => ?_⟩
          exact (hv ⟨i,hi⟩).symm.trans (hw ⟨i,hi.trans_le hh⟩)
        · right
          apply List.prefix_iff_getElem.mpr
          refine ⟨by omega,fun i hi => ?_⟩
          exact (hw ⟨i,hi⟩).symm.trans (hv ⟨i,by omega⟩)
      cases pref with
      | inl hh => exact hne (Subtype.ext (legalG.1 v.2 w.2 hh))
      | inr hh => exact hne (Subtype.ext (legalG.1 w.2 v.2 hh).symm)
    have cylmass (w : List (Fin d)) : μ (wordCylinder w) = ENNReal.ofReal (wordMass p w) := by
      rw [(laws _ hiid).2 w]
      congr 1
      rw [wordMass, ← List.prod_ofFn]
      congr 1
      apply List.ext_getElem
      · simp
      · intro i hi hj
        simp only [List.getElem_ofFn, List.getElem_map, List.get_eq_getElem]
    have unionG : deletedSet G = ⋃ w : G, wordCylinder w.1 := by
      ext x; simp [deletedSet]
    have massG : μ (deletedSet G) = codeMass p G := by
      rw [unionG,measure_iUnion disj (fun w => cm w.1)]
      simp_rw [cylmass]
      rfl
    have greatest : IsGreatest {x : ℝ | ∃ F : Set (List (Fin d)),
        Legal (fun _ => 1) F ∧ x = (codeMass p F).toReal} (codeMass p G).toReal := by
      refine ⟨⟨G,legalG,rfl⟩,?_⟩
      rintro x ⟨F,hF,rfl⟩
      exact ENNReal.toReal_mono (by rw [← massG]; exact measure_ne_top μ _)
        (optimizer.2.2.2 ⟨F,hF,rfl⟩)
    rw [greatest.csSup_eq]
    have um : MeasurableSet (deletedSet G) := MeasurableSet.iUnion (fun w =>
      MeasurableSet.iUnion (fun _ => cm w))
    have comp := measureReal_add_measureReal_compl (μ := μ) um
    have total : μ.real Set.univ = 1 := by simp [Measure.real]
    rw [total] at comp
    have he : μ.real (deletedSet G) = (codeMass p G).toReal := congrArg ENNReal.toReal massG
    have small : (output : ℝ) < (gammas J).1 := by exact_mod_cast outstrict ho
    change ((gammas J).1 : ℝ) ≤ μ.real (deletedSet G)ᶜ at bound
    linarith only [bound,he,comp,small]

#print axioms q_free_historical_rational_certificate

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.EffectiveRationalTransportTail
