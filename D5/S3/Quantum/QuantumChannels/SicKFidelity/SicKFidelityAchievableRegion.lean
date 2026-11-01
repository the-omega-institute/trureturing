/- GID: D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Achievable (k-fidelity, process fidelity) regions and single-Fk non-identifiability. -/

import D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight

/-! # Achievable `(k-fidelity, process fidelity)` regions and single-`F_k` non-identifiability -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityAchievableRegion

open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight

def achievableRegion (n k : ℕ) (ρ : Fin n → Fin 4 → QubitMatrix) : Set (ℝ × ℝ) :=
  {p | ∃ Λ : QubitMap n, Λ.IsCompletelyPositive ∧ Λ.IsTracePreserving ∧
    p = (realKFidelity ρ k Λ, realProcessFidelity Λ)}
def tailCoeff (k w : ℕ) : ℝ := (3 : ℝ)⁻¹ ^ w * (Nat.choose (w - 1) k : ℝ)
def optWeight (n k : ℕ) : ℕ := min n ((3 * k) / 2 + 1)
def extremalAbscissa (n k : ℕ) : ℝ := (-1 : ℝ) ^ k * tailCoeff k (optWeight n k)

open Finset

private abbrev QFam (n : ℕ) := Fin n → Fin 4 → QubitMatrix
private abbrev aRg := achievableRegion
private abbrev tCf := tailCoeff
private abbrev oWt := optWeight
private abbrev eAb := extremalAbscissa
private abbrev pCh {n : ℕ} := @pauliChannel n
private def cLbl (n w : ℕ) : PauliLabel n := fun i => if i.val < w then 3 else 0
private theorem hw_cLbl {n w : ℕ} (hw : w ≤ n) : hammingWeight (cLbl n w) = w := by
  unfold hammingWeight cLbl; let f : Fin w → Fin n := fun j => ⟨j.val, by omega⟩; have himg :
    univ.filter (fun i : Fin n => (if i.val < w then (3 : Fin 4) else 0) ≠ 0) = univ.image f := (by
    ext i; simp only [mem_filter, mem_image, mem_univ, true_and, f]; refine
      ⟨fun hi => ?_, fun ⟨j, hj⟩ => by rw [← hj]; simp [j.isLt]⟩; by_cases hlt : i.val < w;
      (· exact ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩); (· simp [hlt] at hi)); have hf : Function.Injective f
    := fun _ _ h => Fin.ext (congrArg (fun x : Fin n => x.val) h); rw [himg,
    card_image_of_injective univ hf]; simp
private theorem hw_zero (n : ℕ) : hammingWeight (0 : PauliLabel n) = 0 := by simp [hammingWeight]
private theorem pow3_le9 {n : ℕ} (hn2 : 2 ≤ n) : (3 : ℝ)⁻¹ ^ n ≤ 1 / 9 := (pow_le_pow_of_le_one
    (by norm_num) (by norm_num) hn2).trans (by norm_num)
private theorem ext_evn {n k : ℕ} (he : Even k) : eAb n k = tCf k (oWt n k) := by
  unfold eAb extremalAbscissa; rw [he.neg_one_pow, one_mul]
private theorem ext_odd {n k : ℕ} (ho : Odd k) : eAb n k = -tCf k (oWt n k) := by
  unfold eAb extremalAbscissa; rw [ho.neg_one_pow]; ring
private theorem pCh_eval {n : ℕ} (q : PauliLabel n → ℝ) (hq0 : ∀ β, 0 ≤ q β) (hq1 : ∑ β :
    PauliLabel n, q β = 1) : (pCh q).IsCompletelyPositive ∧ (pCh q).IsTracePreserving ∧
    realProcessFidelity (pCh q) = q 0 ∧ ∀ w : ℕ, realWeightSum (pCh q) w = ∑ β ∈ univ.filter (fun β
    : PauliLabel n => hammingWeight β = w), q β := by
  have hch := (pauli_process_matrix_and_fidelity_characterization n).2.2.2.2 q; have htw (β) :
    pauliTwirlWeight (pCh q) β = (q β : ℂ) := (by simpa [pauliTwirlWeight] using hch.1 β β); refine
    ⟨hch.2.1 hq0, hch.2.2 hq1, (by
    unfold realProcessFidelity; rw [(pauli_process_matrix_and_fidelity_characterization n).2.1 (pCh
      q) |>.1, htw 0, Complex.ofReal_re]), fun w => (by
    unfold realWeightSum pauliWeightSum; simp_rw [htw]; rw [← Complex.ofReal_sum,
      Complex.ofReal_re])⟩
private theorem two_pCh {n : ℕ} (k : ℕ) (ρ : QFam n) (hρ : ∀ i, IsQubitSICProjector (ρ i)) {β :
    PauliLabel n} (hβ : 1 ≤ hammingWeight β) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (q : PauliLabel n
    → ℝ) (hq : q = fun γ => if γ = 0 then t else if γ = β then 1 - t else 0) : (pCh
    q).IsCompletelyPositive ∧ (pCh q).IsTracePreserving ∧ (realKFidelity ρ k (pCh q),
    realProcessFidelity (pCh q)) = (t + (-1 : ℝ) ^ k * tCf k (hammingWeight β) * (1 - t), t) := by
  have hβ0 : β ≠ 0 := fun h => (by rw [h, hw_zero] at hβ; omega); have hqs (γ) : q γ = (if γ = 0
    then t else 0) + (if γ = β then 1 - t else 0) := (by
    rw [hq]; by_cases h1 : γ = 0; (· subst h1; simp [hβ0.symm]); (· simp [h1])); have hq0 (γ) : 0 ≤
    q γ := (by rw [hq]; dsimp; split_ifs <;> linarith); have hq1 : ∑ γ, q γ = 1 :=
    (by simp_rw [hqs]; simp [sum_add_distrib]); obtain ⟨hCP, hTP, hF, hW⟩ := pCh_eval q hq0 hq1;
    refine ⟨hCP, hTP, ?_⟩; rw [show realProcessFidelity (pCh q) = t by rw [hF, hq]; simp]; congr 1;
    rw [((kFidelity_eq_pauliWeight_alternating_sum n k ρ hρ (pCh q)).2.2.2 hCP).2]; have hW0 :
    realWeightSum (pCh q) 0 = t := (by
    rw [hW 0, show univ.filter (fun γ : PauliLabel n => hammingWeight γ = 0) = {0} from
      (by ext γ; simp [hammingWeight, card_eq_zero, filter_eq_empty_iff, funext_iff]),
      sum_singleton, hq]; simp)
  have hWw (w) (hw : w ∈ Icc 1 n) : realWeightSum (pCh q) w = if w = hammingWeight β then 1 - t
    else 0 := by
    rw [hW w]; simp_rw [hqs]; rw [sum_add_distrib, sum_eq_zero fun x hx => (by
      by_cases hx0 : x = 0
      · subst hx0; have := (mem_filter.mp hx).2; have := (mem_Icc.mp hw).1; rw [hw_zero] at *; omega
      · simp [hx0]), zero_add, sum_ite_eq']; simp [eq_comm (a := w)]
  have hβle : hammingWeight β ≤ n := le_trans (card_filter_le _ _) (by simp); rw [hW0]; congr 1; rw
    [sum_congr rfl fun w hw => by rw [hWw w hw]]; simp_rw [mul_ite, mul_zero]; rw [sum_ite_eq'];
    simp only [mem_Icc, hβ, hβle, and_self, ↓reduceIte, tCf, tailCoeff]; ring
private theorem vImg_eq (n k : ℕ) (ρ : QFam n) (hρ : ∀ i, IsQubitSICProjector (ρ i)) :
    let V : Fin (n + 1) → ℝ × ℝ :=
      fun i => if i.val = 0 then (1, 1) else ((-1 : ℝ) ^ k * tCf k i.val, 0)
    aRg n k ρ = convexHull ℝ (Set.range V) := by
  intro V; have hch := pauli_process_matrix_and_fidelity_characterization n
  have hpair (Λ : QubitMap n) (hCP : Λ.IsCompletelyPositive) : (realKFidelity ρ k Λ,
    realProcessFidelity Λ) = ∑ i : Fin (n + 1), realWeightSum Λ i.val • V i := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sum, Prod.smul_fst, V]; simp_rw [apply_ite Prod.fst, smul_eq_mul]; rw
        [Fin.sum_univ_eq_sum_range (fun w => realWeightSum Λ w * (if w = 0 then (1 : ℝ) else (-1 :
        ℝ) ^ k * tCf k w)) (n + 1), show range (n + 1) = insert 0 (Icc 1 n) from
        (by ext w; simp only [mem_range, mem_insert, mem_Icc]; omega), sum_insert (by simp),
        ((kFidelity_eq_pauliWeight_alternating_sum n k ρ hρ Λ).2.2.2 hCP).2]; simp only
        [↓reduceIte, mul_one]; congr 1; rw [mul_sum]; exact sum_congr rfl fun w hw => (by
        have hw0 : w ≠ 0 := (by have := (mem_Icc.mp hw).1; omega); simp only [hw0, ↓reduceIte];
          dsimp [tCf, tailCoeff]; ring)
    · simp only [Prod.snd_sum, Prod.smul_snd, V]; simp_rw [apply_ite Prod.snd, smul_eq_mul]
      rw [Fintype.sum_eq_single (0 : Fin (n + 1)) fun i hi =>
        (by have : i.val ≠ 0 := fun h => hi (Fin.ext h); simp [this])]
      simp only [Fin.val_zero, ↓reduceIte, mul_one]; exact Complex.ofReal_inj.mp (by
        rw [(hch.2.2.2.1 Λ hCP).2.2, ((hch.2.2.2.1 Λ hCP).2.1 0).1, (hch.2.1 Λ).1, (hch.2.1 Λ).2.1])
  let S := {p : ℝ × ℝ | ∃ P : Fin (n + 1) → ℝ, (∀ i, 0 ≤ P i) ∧ ∑ i, P i = 1 ∧ ∑ i, P i • V i = p}
  have hRS : aRg n k ρ = S := by
    ext p; constructor
    · rintro ⟨Λ, hCP, hTP, rfl⟩; have hP1 : ∑ i : Fin (n + 1), realWeightSum Λ i.val = 1 := (by
        rw [Fin.sum_univ_eq_sum_range (fun w => realWeightSum Λ w) (n + 1)]; simpa [realWeightSum]
          using congrArg Complex.re (((hch.2.2.1 Λ).2 hTP).2)); exact ⟨fun i => realWeightSum Λ
        i.val, fun i => ((hch.2.2.2.1 Λ hCP).2.1 i.val).2, hP1, (hpair Λ hCP).symm⟩
    · rintro ⟨P, hP0, hP1, rfl⟩; let q (β : PauliLabel n) : ℝ := ∑ i : Fin (n + 1), if β = cLbl n
        i.val then P i else 0; have hq0 (β) : 0 ≤ q β := sum_nonneg fun i _ =>
        (by by_cases h : β = cLbl n i.val <;> simp [h, hP0 i]); have hq1 : ∑ β, q β = 1 :=
        (by dsimp [q]; rw [sum_comm]; simp [hP1]); obtain ⟨hCP, hTP, _, hW⟩ := pCh_eval q hq0 hq1
      have hWi (i : Fin (n + 1)) : realWeightSum (pCh q) i.val = P i := by
        rw [hW i.val]; dsimp [q]; rw [sum_comm, Fintype.sum_eq_single i fun j hj =>
          sum_eq_zero fun β hβ => (by
            by_cases hEq : β = cLbl n j.val
            · subst hEq; exfalso; apply hj; apply Fin.ext; have hw := (mem_filter.mp hβ).2
              rwa [hw_cLbl (Nat.lt_succ_iff.mp j.isLt)] at hw
            · simp [hEq]), sum_eq_single (cLbl n i.val)]
        · simp
        · intro β _ hne; simp [hne]
        · intro hnot; exfalso; apply hnot; simp [hw_cLbl (Nat.lt_succ_iff.mp i.isLt)]
      exact ⟨pCh q, hCP, hTP,
        (sum_congr rfl fun i _ => by rw [← hWi i]).trans (hpair (pCh q) hCP).symm⟩
  rw [hRS]; refine Set.Subset.antisymm (fun _ ⟨P, hP0, hP1, hPv⟩ => hPv ▸ (convex_convexHull ℝ
    (Set.range V)).sum_mem (fun i _ => hP0 i) hP1 (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩))
    (convexHull_min ?_ ?_)
  · rintro _ ⟨i, rfl⟩; exact ⟨fun j => if j = i then 1 else 0,
      fun j => by dsimp; split_ifs <;> norm_num, by simp, by simp [ite_smul]⟩
  · rintro _ ⟨P₁, hP₁0, hP₁1, rfl⟩ _ ⟨P₂, hP₂0, hP₂1, rfl⟩ a b ha hb hab
    exact ⟨fun i => a * P₁ i + b * P₂ i,
      fun i => add_nonneg (mul_nonneg ha (hP₁0 i)) (mul_nonneg hb (hP₂0 i)),
      (by simp_rw [sum_add_distrib, ← mul_sum, hP₁1, hP₂1, mul_one, hab]),
      by simp_rw [add_smul, mul_smul, sum_add_distrib, ← smul_sum]⟩
private theorem tri_hull {a b : ℝ} (hab : a ≤ b) : convexHull ℝ ({(1, 1), (a, 0), (b, 0)} : Set (ℝ
    × ℝ)) = {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ a * (1 - p.2) ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ b * (1 - p.2)}
    := by
  let S : Set (ℝ × ℝ) := {(1, 1), (a, 0), (b, 0)}; apply Set.Subset.antisymm
  · refine convexHull_min (fun p hp => ?_) (fun p hp q hq u v hu hv huv => ?_)
    · rcases hp with rfl | rfl | rfl <;> dsimp <;> exact
        ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rcases hp with ⟨hp0, hp1, hpa, hpb⟩; rcases hq with ⟨hq0, hq1, hqa, hqb⟩; have hlin (c : ℝ) :
        c * (1 - (u * p.2 + v * q.2)) = u * (c * (1 - p.2)) + v * (c * (1 - q.2)) :=
        (by linear_combination -c * huv); have := mul_le_mul_of_nonneg_left hpa hu; have :=
        mul_le_mul_of_nonneg_left hqa hv; have := mul_le_mul_of_nonneg_left hpb hu; have :=
        mul_le_mul_of_nonneg_left hqb hv; have := mul_le_mul_of_nonneg_left hp1 hu; have :=
        mul_le_mul_of_nonneg_left hq1 hv; have := mul_nonneg hu hp0; have := mul_nonneg hv hq0
      exact ⟨by dsimp; linarith, by dsimp; linarith,
        by dsimp; rw [hlin a]; linarith, by dsimp; rw [hlin b]; linarith⟩
  · rintro ⟨x, y⟩ ⟨hy0, hy1, hya, hyb⟩; have h1m : ((1 : ℝ), (1 : ℝ)) ∈ convexHull ℝ S :=
      subset_convexHull ℝ S (by simp [S]); have ham : (a, (0 : ℝ)) ∈ convexHull ℝ S :=
      subset_convexHull ℝ S (by simp [S]); have hbm : (b, (0 : ℝ)) ∈ convexHull ℝ S :=
      subset_convexHull ℝ S (by simp [S])
    rcases eq_or_lt_of_le hy1 with rfl | hylt
    · rw [show x = 1 by linarith]; exact h1m
    · have h1y : 0 < 1 - y := (by linarith); let z : ℝ := (x - y) / (1 - y)
      have haz : a ≤ z := (le_div_iff₀ h1y).mpr hya; have hzb : z ≤ b := (div_le_iff₀ h1y).mpr hyb
      have hzm : (z, (0 : ℝ)) ∈ convexHull ℝ S := (by
        rcases eq_or_lt_of_le hab with rfl | hablt; (· rw [le_antisymm hzb haz]; exact ham);
          (· exact (by
          let s : ℝ := (b - z) / (b - a); have hs1 : 0 ≤ 1 - s :=
            (by have := (div_le_one (by linarith)).mpr (by linarith : b - z ≤ b - a); linarith);
            have heq : s • (a, (0 : ℝ)) + (1 - s) • (b, (0 : ℝ)) = (z, (0 : ℝ)) := (by
            ext <;> dsimp [s]; (· exact (by field_simp [show b - a ≠ 0 by linarith]; ring));
              (· ring)); rw [← heq]; exact (convex_convexHull ℝ S) ham hbm (div_nonneg
            (by linarith) (by linarith)) hs1 (by ring)))); have hxy : y • ((1 : ℝ), (1 : ℝ)) + (1 -
        y) • (z, (0 : ℝ)) = (x, y) :=
        (by ext <;> dsimp [z]; (· field_simp [ne_of_gt h1y]; ring); (· ring)); rw [← hxy]; exact
        (convex_convexHull ℝ S) h1m hzm hy0 (le_of_lt h1y) (by ring)
private theorem tri_frac {a b : ℝ} (hab : a < b) (hb1 : b < 1) (p : ℝ × ℝ) : p ∈ convexHull ℝ ({(1,
    1), (a, 0), (b, 0)} : Set (ℝ × ℝ)) ↔ 0 ≤ p.2 ∧ (p.1 - b) / (1 - b) ≤ p.2 ∧ p.2 ≤ (p.1 - a) / (1
    - a) := by
  have h1b : 0 < 1 - b := (by linarith); have h1a : 0 < 1 - a := (by linarith); rw [tri_hull
    (le_of_lt hab)]; dsimp
  refine ⟨fun ⟨h0, _, ha, hb⟩ => ⟨h0, (div_le_iff₀ h1b).mpr (by linarith), (le_div_iff₀ h1a).mpr
    (by linarith)⟩, fun ⟨h0, hb, ha⟩ => ?_⟩
  have hb' := (div_le_iff₀ h1b).mp hb; have ha' := (le_div_iff₀ h1a).mp ha
  have hp1 := nonneg_of_mul_nonneg_right (by linarith : 0 ≤ (b - a) * (1 - p.2)) (by linarith);
    exact ⟨h0, by linarith, by linarith, by linarith⟩

theorem achievableRegion_zero_characterization (n : ℕ) (hn : 1 ≤ n)
    (ρ : Fin n → Fin 4 → QubitMatrix) (hρ : ∀ i : Fin n, IsQubitSICProjector (ρ i)) :
    achievableRegion n 0 ρ =
      convexHull ℝ ({(1, 1), ((3 : ℝ)⁻¹ ^ n, 0), ((3 : ℝ)⁻¹, 0)} : Set (ℝ × ℝ)) ∧
    (2 ≤ n → ∀ p : ℝ × ℝ, p ∈ achievableRegion n 0 ρ ↔ 0 ≤ p.2 ∧
      1 - (3 / 2 : ℝ) * (1 - p.1) ≤ p.2 ∧ p.2 ≤ (p.1 - (3 : ℝ)⁻¹ ^ n) / (1 - (3 : ℝ)⁻¹ ^ n)) ∧
    (n = 1 → ∀ p : ℝ × ℝ, p ∈ achievableRegion n 0 ρ ↔
      p.2 = 1 - (3 / 2 : ℝ) * (1 - p.1) ∧ (3 : ℝ)⁻¹ ≤ p.1 ∧ p.1 ≤ 1) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      let q : PauliLabel n → ℝ := fun γ => if γ = 0 then t else if γ = (fun _ => 3) then 1 - t else
        0
      (pauliChannel q).IsCompletelyPositive ∧ (pauliChannel q).IsTracePreserving ∧
        (realKFidelity ρ 0 (pauliChannel q), realProcessFidelity (pauliChannel q)) =
          (t + (1 - t) * (3 : ℝ)⁻¹ ^ n, t)) ∧
    (∀ β : PauliLabel n, hammingWeight β = 1 → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      let q : PauliLabel n → ℝ := fun γ => if γ = 0 then t else if γ = β then 1 - t else 0
      (pauliChannel q).IsCompletelyPositive ∧ (pauliChannel q).IsTracePreserving ∧
        (realKFidelity ρ 0 (pauliChannel q), realProcessFidelity (pauliChannel q)) =
          (t + (1 - t) * (3 : ℝ)⁻¹, t)) ∧
    (2 ≤ n → ∀ x : ℝ, (3 : ℝ)⁻¹ ^ n ≤ x → x ≤ 1 →
      IsGreatest {y : ℝ | (x, y) ∈ achievableRegion n 0 ρ}
        ((x - (3 : ℝ)⁻¹ ^ n) / (1 - (3 : ℝ)⁻¹ ^ n)) ∧
      (x < 1 → (x - (3 : ℝ)⁻¹ ^ n) / (1 - (3 : ℝ)⁻¹ ^ n) < x) ∧
      x - (x - (3 : ℝ)⁻¹ ^ n) / (1 - (3 : ℝ)⁻¹ ^ n) =
        (1 - x) * (3 : ℝ)⁻¹ ^ n / (1 - (3 : ℝ)⁻¹ ^ n) ∧
      IsLeast {y : ℝ | (x, y) ∈ achievableRegion n 0 ρ} (max 0 (1 - (3 / 2 : ℝ) * (1 - x)))) := by
  have han : (3 : ℝ)⁻¹ ^ n ≤ (3 : ℝ)⁻¹ :=
    (by simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹) (by norm_num) hn); let
    S : Set (ℝ × ℝ) := {(1, 1), ((3 : ℝ)⁻¹ ^ n, 0), ((3 : ℝ)⁻¹, 0)}; have hch : achievableRegion n
    0 ρ = convexHull ℝ S := (by
    change aRg n 0 ρ = _; rw [vImg_eq n 0 ρ hρ]; refine Set.Subset.antisymm (convexHull_min (by
      rintro _ ⟨i, rfl⟩; by_cases hi0 : i.val = 0;
        (· exact (by simp only [hi0, ↓reduceIte]; exact subset_convexHull ℝ S (by simp [S])));
        (· exact (by
        simp only [hi0, ↓reduceIte, pow_zero, one_mul, tailCoeff, Nat.choose_zero_right,
          Nat.cast_one, mul_one]; rw [tri_hull han]; have hlo : (3 : ℝ)⁻¹ ^ n ≤ (3 : ℝ)⁻¹ ^ i.val
          := pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.lt_succ_iff.mp i.isLt); have hhi
          : (3 : ℝ)⁻¹ ^ i.val ≤ (3 : ℝ)⁻¹ := (by
          simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹) (by norm_num)
            (Nat.one_le_iff_ne_zero.mpr hi0)); exact
          ⟨le_rfl, zero_le_one, by simpa using hlo, by simpa using hhi⟩))) (convex_convexHull ℝ S))
      (convexHull_min (by
      rintro p (rfl | rfl | rfl); (· exact (by exact subset_convexHull ℝ _ ⟨0, by simp⟩));
        (· exact (by
        exact subset_convexHull ℝ _
          ⟨⟨n, Nat.lt_succ_self n⟩, by simp [Nat.ne_of_gt hn, tailCoeff]⟩)); (· exact (by
        exact subset_convexHull ℝ _ ⟨⟨1, Nat.succ_lt_succ hn⟩, by simp [tailCoeff]⟩)))
      (convex_convexHull ℝ _))); have hiff2 (hn2 : 2 ≤ n) (p : ℝ × ℝ) : p ∈ achievableRegion n 0 ρ
    ↔ 0 ≤ p.2 ∧ 1 - (3 / 2 : ℝ) * (1 - p.1) ≤ p.2 ∧ p.2 ≤ (p.1 - (3 : ℝ)⁻¹ ^ n) / (1 - (3 : ℝ)⁻¹ ^
    n) := (by
    have := pow3_le9 hn2; rw [hch, tri_frac (by linarith) (by norm_num) p,
      show (p.1 - (3 : ℝ)⁻¹) / (1 - (3 : ℝ)⁻¹) = 1 - (3 / 2 : ℝ) * (1 - p.1) by norm_num; ring])
  refine ⟨hch, hiff2, fun hn1 p => ?_, fun t ht0 ht1 => ?_, fun β hβ t ht0 ht1 => ?_, fun hn2 x hx0
    hx1 => ?_⟩
  · subst hn1; rw [hch]; dsimp [S]; rw [pow_one, tri_hull le_rfl]; dsimp; exact ⟨fun ⟨_, _, _, _⟩
      => ⟨by linarith, by linarith, by linarith⟩, fun ⟨_, _, _⟩ =>
      ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
  · intro q; have hwZ : hammingWeight (fun _ : Fin n => (3 : Fin 4)) = n := (by
      rw [show (fun _ : Fin n => (3 : Fin 4)) = cLbl n n by ext i; simp [cLbl, i.isLt]]; exact
        hw_cLbl le_rfl); obtain ⟨hCP, hTP, hp⟩ := two_pCh 0 ρ hρ (β := fun _ => 3) (by omega) ht0
      ht1 q rfl; exact ⟨hCP, hTP, by rw [hp, hwZ]; simp [tailCoeff, mul_comm]⟩
  · intro q; obtain ⟨hCP, hTP, hp⟩ := two_pCh 0 ρ hρ (β := β) (by omega) ht0 ht1 q rfl; exact
      ⟨hCP, hTP, by rw [hp, hβ]; simp [tailCoeff, mul_comm]⟩
  · have h9 := pow3_le9 hn2; have han0 : 0 < (3 : ℝ)⁻¹ ^ n := (by positivity); have hden : 0 < 1 -
      (3 : ℝ)⁻¹ ^ n := (by linarith); let ym : ℝ := (x - (3 : ℝ)⁻¹ ^ n) / (1 - (3 : ℝ)⁻¹ ^ n); have
      hym0 : 0 ≤ ym := div_nonneg (by linarith) (le_of_lt hden)
    have hlu : 1 - (3 / 2 : ℝ) * (1 - x) ≤ ym := (le_div_iff₀ hden).mpr (by
      linarith [show (x - (3 : ℝ)⁻¹ ^ n) - (1 - (3 / 2 : ℝ) * (1 - x)) * (1 - (3 : ℝ)⁻¹ ^ n) =
        (1 - x) * (1 / 2 - (3 / 2 : ℝ) * (3 : ℝ)⁻¹ ^ n) by ring,
        mul_nonneg (by linarith : 0 ≤ 1 - x)
        (by linarith : 0 ≤ 1 / 2 - (3 / 2 : ℝ) * (3 : ℝ)⁻¹ ^ n)])
    have hgap : x - ym = (1 - x) * (3 : ℝ)⁻¹ ^ n / (1 - (3 : ℝ)⁻¹ ^ n) := mul_right_cancel₀
      (ne_of_gt hden) (by
      dsimp [ym]; rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hden), div_mul_cancel₀ _ (ne_of_gt
        hden)]; ring); exact ⟨⟨(hiff2 hn2 _).mpr ⟨hym0, hlu, le_rfl⟩, fun y hy => ((hiff2 hn2 (x,
      y)).mp hy).2.2⟩, fun hxlt => (by
        dsimp [ym] at hgap; have := div_pos (mul_pos (by linarith : 0 < 1 - x) han0) hden
        linarith [hgap]), hgap,
      ⟨(hiff2 hn2 _).mpr ⟨le_max_left _ _, le_max_right _ _, max_le hym0 hlu⟩, fun
      y hy => max_le ((hiff2 hn2 (x, y)).mp hy).1 ((hiff2 hn2 (x, y)).mp hy).2.1⟩⟩

private theorem ch_le2 (m k : ℕ) : m.choose k ≤ 2 ^ m := by
  induction m generalizing k with
  | zero => cases k <;> simp
  | succ m ih => cases k with
    | zero => exact Nat.one_le_two_pow
    | succ k =>
      rw [Nat.choose_succ_succ, Nat.pow_succ]; have := ih k; have := ih (k + 1); change m.choose k
        + m.choose (k + 1) ≤ 2 ^ m * 2; omega
private theorem tc_lt1 {k w : ℕ} (hw : 1 ≤ w) : tCf k w < 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, (Nat.sub_add_cancel hw).symm⟩; unfold tCf tailCoeff;
    simp only [Nat.add_sub_cancel]; have hch : (m.choose k : ℝ) ≤ (2 : ℝ) ^ m :=
    (by exact_mod_cast ch_le2 m k); have h1 : (3 : ℝ)⁻¹ ^ (m + 1) * (m.choose k : ℝ) ≤ (3 : ℝ)⁻¹ *
    (2 / 3 : ℝ) ^ m := (mul_le_mul_of_nonneg_left hch (by positivity)).trans_eq
    (by rw [pow_succ', div_eq_mul_inv, mul_pow]; norm_num; ring); nlinarith [pow_le_one₀
    (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num) (n := m)]
private theorem tc_step {k w : ℕ} (hw : k + 1 ≤ w) : 3 * ((w - k : ℕ) : ℝ) * tCf k (w + 1) = (w :
    ℝ) * tCf k w := by
  obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, (Nat.sub_add_cancel (by omega)).symm⟩; have hcast :
    ((m.choose k : ℝ) * ((m + 1 : ℕ) : ℝ)) = ((m + 1).choose k : ℝ) * ((m + 1 - k : ℕ) : ℝ) :=
    (by exact_mod_cast Nat.choose_mul_succ_eq m k); unfold tCf tailCoeff; simp only
    [Nat.add_sub_cancel]
  calc 3 * ((m + 1 - k : ℕ) : ℝ) * ((3 : ℝ)⁻¹ ^ (m + 1 + 1) * ((m + 1).choose k : ℝ))
      = (3 : ℝ)⁻¹ ^ (m + 1) * (((m + 1).choose k : ℝ) * ((m + 1 - k : ℕ) : ℝ)) :=
        (by rw [pow_succ]; norm_num; ring)
    _ = ((m + 1 : ℕ) : ℝ) * ((3 : ℝ)⁻¹ ^ (m + 1) * (m.choose k : ℝ)) := (by rw [← hcast]; ring)
private theorem tc_pos {k w : ℕ} (hw : k + 1 ≤ w) : 0 < tCf k w := mul_pos (by positivity)
    (by exact_mod_cast Nat.choose_pos (by omega))
private theorem tc_max {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k + 1 ≤ n) : (0 < tCf k (oWt n k) ∧ tCf k
    (oWt n k) < 1) ∧ (∀ w ∈ Icc 1 n, tCf k w ≤ tCf k (oWt n k)) ∧ (Icc 1 n).filter (fun w => tCf k
    w = tCf k (oWt n k)) = @ite _ (Even k ∧ 3 * k / 2 + 1 ≤ n) (Classical.propDecidable _)
    {3 * k / 2, 3 * k / 2 + 1} {oWt n k} := by
  have hlo : k + 1 ≤ oWt n k := (by unfold oWt optWeight; omega); have hhi : oWt n k ≤ n :=
    Nat.min_le_left _ _; have hpos : 0 < tCf k (oWt n k) := tc_pos hlo; have hlt1 : tCf k (oWt n k)
    < 1 := tc_lt1 (by omega); have hinc {w : ℕ} (hw1 : k + 1 ≤ w) (hw2 : 2 * w < 3 * k) : tCf k w <
    tCf k (w + 1) := (by
    have h1 : ((3 * (w - k) : ℕ) : ℝ) < (w : ℝ) := (by exact_mod_cast (by omega : 3 * (w - k) < w));
      rw [Nat.cast_mul, Nat.cast_ofNat] at h1; nlinarith [tc_step hw1, tc_pos (k := k) (w := w + 1)
      (by omega)])
  have heqs {w : ℕ} (hw1 : k + 1 ≤ w) (hw2 : 2 * w = 3 * k) : tCf k w = tCf k (w + 1) := by
    have h1 : ((3 * (w - k) : ℕ) : ℝ) = (w : ℝ) := (by exact_mod_cast (by omega : 3 * (w - k) = w))
    rw [Nat.cast_mul, Nat.cast_ofNat] at h1; have hst := tc_step hw1; rw [h1] at hst; exact
      mul_left_cancel₀ (Nat.cast_ne_zero.mpr (by omega)) hst.symm
  have hdec {w : ℕ} (hw1 : k + 1 ≤ w) (hw2 : 3 * k < 2 * w) : tCf k (w + 1) < tCf k w := (by
    have h1 : (w : ℝ) < ((3 * (w - k) : ℕ) : ℝ) :=
      (by exact_mod_cast (by omega : w < 3 * (w - k))); rw [Nat.cast_mul, Nat.cast_ofNat] at h1;
      nlinarith [tc_step hw1, tc_pos (k := k) (w := w + 1) (by omega)])
  have hup : ∀ d u, k + 1 ≤ u → u + d ≤ 3 * k / 2 + 1 → tCf k u ≤ tCf k (u + d) ∧ (tCf k u = tCf k
    (u + d) → d = 0 ∨ (Even k ∧ u = 3 * k / 2 ∧ d = 1)) := by
    intro d; induction d with
    | zero => intro u _ _; exact ⟨le_rfl, fun _ => Or.inl rfl⟩
    | succ d ih =>
      intro u hu1 hud; obtain ⟨hle, heq_ih⟩ := ih u hu1 (by omega); by_cases h2 : 2 * (u + d) < 3 *
        k; (· exact (by have hst := hinc (by omega : k + 1 ≤ u + d) h2; exact ⟨le_of_lt
                          (lt_of_le_of_lt hle hst), fun h => absurd h (ne_of_lt (lt_of_le_of_lt hle
                          hst))⟩)); (· exact (by
        have hst := heqs (by omega : k + 1 ≤ u + d) (by omega : 2 * (u + d) = 3 * k); refine
          ⟨le_trans hle (le_of_eq hst), fun he => ?_⟩; rcases heq_ih (he.trans hst.symm) with rfl |
          ⟨⟨m, rfl⟩, rfl, rfl⟩; (· exact (by exact Or.inr ⟨⟨u - k, by omega⟩, by omega, rfl⟩));
          (· omega)))
  have hdn : ∀ d u, 3 * k / 2 + 1 ≤ u → tCf k (u + d) ≤ tCf k u ∧ (tCf k (u + d) = tCf k u → d = 0)
    := by
    intro d; induction d with
    | zero => intro u _; exact ⟨le_rfl, fun _ => rfl⟩
    | succ d ih =>
      intro u hu; have hst := hdec (by omega : k + 1 ≤ u + d) (by omega : 3 * k < 2 * (u + d));
        exact ⟨le_of_lt (lt_of_lt_of_le hst (ih u hu).1), fun h => absurd h (ne_of_lt
        (lt_of_lt_of_le hst (ih u hu).1))⟩
  have hmax (w) (hw : w ∈ Icc 1 n) : tCf k w ≤ tCf k (oWt n k) ∧ (tCf k w = tCf k (oWt n k) ↔ w =
    oWt n k ∨ (Even k ∧ 3 * k / 2 + 1 ≤ n ∧ w = 3 * k / 2)) := by
    obtain ⟨hw1, hwn⟩ := mem_Icc.mp hw; by_cases hwk : w ≤ k
    · rw [show tCf k w = 0 from
        (by unfold tCf tailCoeff; simp [Nat.choose_eq_zero_of_lt (by omega : w - 1 < k)])]; refine
        ⟨le_of_lt hpos, ⟨fun h => absurd h.symm (ne_of_gt hpos), fun h => ?_⟩⟩; exfalso; rcases h
        with rfl | ⟨⟨m, rfl⟩, _, rfl⟩ <;> omega
    · by_cases hwopt : w ≤ oWt n k
      · obtain ⟨h1, h2⟩ := hup (oWt n k - w) w (by omega) (by unfold oWt optWeight at *; omega)
        rw [Nat.add_sub_of_le hwopt] at h1 h2; refine ⟨h1, ⟨fun he => (by
          rcases h2 he with hd0 | ⟨⟨m, rfl⟩, rfl, hd1⟩; (· exact (by exact Or.inl (by omega)));
            (· exact (by exact Or.inr ⟨⟨m, rfl⟩, by unfold oWt optWeight at hd1; omega, rfl⟩))),
          fun h => (by
          rcases h with rfl | ⟨⟨m, rfl⟩, hmn, rfl⟩; (· rfl); (· exact (by
            rw [show oWt n (m + m) = 3 * (m + m) / 2 + 1 from Nat.min_eq_right hmn]; exact heqs
              (by omega) (by omega))))⟩⟩
      · obtain ⟨h1, h2⟩ := hdn (w - oWt n k) (oWt n k) (by unfold oWt optWeight at hwopt ⊢; omega);
          rw [Nat.add_sub_of_le (by omega)] at h1 h2; refine ⟨h1, ⟨fun he => Or.inl
          (by have := h2 he; omega), fun h => ?_⟩⟩; exfalso; rcases h with rfl | ⟨⟨m, rfl⟩, _, rfl⟩
          <;> (unfold oWt optWeight at hwopt; omega)
  refine ⟨⟨hpos, hlt1⟩, fun w hw => (hmax w hw).1, ?_⟩; ext w; by_cases hc : Even k ∧ 3 * k / 2 + 1
    ≤ n; (· exact (by
    simp only [hc, and_self, ↓reduceIte, mem_filter, mem_insert, mem_singleton]; have hopt_eq : oWt
      n k = 3 * k / 2 + 1 := Nat.min_eq_right hc.2; refine ⟨fun ⟨hw, he⟩ => (by
      rcases (hmax w hw).2.mp he with rfl | ⟨_, _, rfl⟩; (· exact Or.inr hopt_eq);
        (· exact Or.inl rfl)), fun h => (by
      rcases h with h | h <;> subst h; (· exact (by
        rcases hc.1 with ⟨m, rfl⟩; have hw : 3 * (m + m) / 2 ∈ Icc 1 n := mem_Icc.mpr
          ⟨by omega, by omega⟩; exact ⟨hw, (hmax _ hw).2.mpr (Or.inr ⟨⟨m, rfl⟩, hc.2, rfl⟩)⟩));
        (· exact (by exact ⟨mem_Icc.mpr ⟨by omega, hc.2⟩, by rw [hopt_eq]⟩)))⟩)); (· exact (by
    simp only [hc, ↓reduceIte, mem_filter, mem_singleton]; refine ⟨fun ⟨hw, he⟩ => (by
      rcases (hmax w hw).2.mp he with rfl | ⟨hev, hle, _⟩; (· rfl);
        (· exact absurd ⟨hev, hle⟩ hc)), fun h =>
      (by subst h; exact ⟨mem_Icc.mpr ⟨by omega, hhi⟩, rfl⟩)⟩))

theorem achievableRegion_intermediate_and_high_characterization (n k : ℕ) (ρ : Fin n → Fin 4 →
    QubitMatrix) (hρ : ∀ i : Fin n, IsQubitSICProjector (ρ i)) : (1 ≤ k ∧ k + 1 ≤ n → (0 <
    tailCoeff k (optWeight n k) ∧ tailCoeff k (optWeight n k) < 1) ∧ (∀ w ∈ Finset.Icc 1 n,
    tailCoeff k w ≤ tailCoeff k (optWeight n k)) ∧ (Finset.Icc 1 n).filter (fun w => tailCoeff k w
    = tailCoeff k (optWeight n k)) = (@ite _ (Even k ∧ 3 * k / 2 + 1 ≤ n)
    (Classical.propDecidable _) {3 * k / 2, 3 * k / 2 + 1} {optWeight n k}) ∧
    achievableRegion n k ρ = convexHull ℝ ({(1, 1), (0, 0),
    (extremalAbscissa n k, 0)} : Set (ℝ × ℝ)) ∧ (Odd k → ∀ p : ℝ × ℝ, p ∈ achievableRegion n k ρ ↔
    0 ≤ p.2 ∧ p.1 ≤ p.2 ∧ p.2 ≤ (p.1 - extremalAbscissa n k) / (1 - extremalAbscissa n k)) ∧ (Even
    k → ∀ p : ℝ × ℝ, p ∈ achievableRegion n k ρ ↔ 0 ≤ p.2 ∧ (p.1 - extremalAbscissa n k) / (1 -
    extremalAbscissa n k) ≤ p.2 ∧ p.2 ≤ p.1) ∧ (∀ p : ℝ × ℝ, p ∈ achievableRegion n k ρ → 0 ≤ p.2 ∧
    p.2 ≤ 1) ∧ (MatrixMap.IsCompletelyPositive (LinearMap.id : QubitMap n) ∧
    MatrixMap.IsTracePreserving (LinearMap.id : QubitMap n) ∧ (realKFidelity ρ k (LinearMap.id :
    QubitMap n), realProcessFidelity (LinearMap.id : QubitMap n)) = (1, 1)) ∧ (∀ β : PauliLabel n,
    hammingWeight β = 1 → (pauliChannel (fun γ => if γ = β then 1 else 0)).IsCompletelyPositive ∧
    (pauliChannel (fun γ => if γ = β then 1 else 0)).IsTracePreserving ∧ (realKFidelity ρ k
    (pauliChannel (fun γ => if γ = β then 1 else 0)), realProcessFidelity (pauliChannel (fun γ =>
    if γ = β then 1 else 0))) = (0, 0)) ∧ (∃ β : PauliLabel n, hammingWeight β = optWeight n k) ∧
    (∀ β : PauliLabel n, hammingWeight β = optWeight n k → (pauliChannel (fun γ => if γ = β then 1
    else 0)).IsCompletelyPositive ∧ (pauliChannel (fun γ => if γ = β then 1 else
    0)).IsTracePreserving ∧ (realKFidelity ρ k (pauliChannel (fun γ => if γ = β then 1 else 0)),
    realProcessFidelity (pauliChannel (fun γ => if γ = β then 1 else 0))) = (extremalAbscissa n k,
    0))) ∧ (1 ≤ n ∧ n ≤ k → achievableRegion n k ρ = convexHull ℝ ({(0, 0), (1, 1)} : Set (ℝ × ℝ))
    ∧ achievableRegion n k ρ = {p : ℝ × ℝ | p.1 = p.2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}) := by
  let q0 (γ : PauliLabel n) : ℝ := if γ = 0 then 1 else 0; have hid_eq : pCh q0 = (LinearMap.id :
    QubitMap n) := (by
    have hp0 : pauliN n 0 = 1 :=
      (by ext x y; simp [pauliN, pauli1, Matrix.one_apply, prod_boole, funext_iff]); ext X u v;
      simp [pCh, pauliChannel, q0, ite_smul, hp0])
  constructor
  · rintro ⟨hk1, hkn⟩; obtain ⟨⟨hpos, hlt1⟩, hmax, hfilt⟩ := tc_max hk1 hkn; let S : Set (ℝ × ℝ) :=
      {(1, 1), (0, 0), (eAb n k, 0)}
    have hch : aRg n k ρ = convexHull ℝ S := by
      rw [vImg_eq n k ρ hρ]
      refine Set.Subset.antisymm (convexHull_min ?_ (convex_convexHull ℝ S))
        (convexHull_min ?_ (convex_convexHull ℝ _))
      · rintro _ ⟨i, rfl⟩; by_cases hi0 : i.val = 0;
          (· exact (by simp only [hi0, ↓reduceIte]; exact subset_convexHull ℝ S (by simp [S])));
          (· exact (by
          simp only [hi0, ↓reduceIte]; have him : i.val ∈ Icc 1 n := mem_Icc.mpr
            ⟨Nat.one_le_iff_ne_zero.mpr hi0, Nat.lt_succ_iff.mp i.isLt⟩; let s : ℝ := tCf k i.val /
            tCf k (oWt n k); have hs0 : 0 ≤ s := div_nonneg (by unfold tCf tailCoeff; positivity)
            (le_of_lt hpos); have hs1 : 0 ≤ 1 - s :=
            (by have := (div_le_one hpos).mpr (hmax i.val him); linarith); have heq : (1 - s) • ((0
            : ℝ), (0 : ℝ)) + s • (eAb n k, (0 : ℝ)) = ((-1 : ℝ) ^ k * tCf k i.val, (0 : ℝ)) := (by
            ext <;> dsimp [s, eAb, extremalAbscissa]; (· field_simp [ne_of_gt hpos]; ring);
              (· ring)); rw [← heq]; exact (convex_convexHull ℝ S) (subset_convexHull ℝ S
            (by simp [S])) (subset_convexHull ℝ S (by simp [S])) hs1 hs0 (by ring)))
      · rintro p (rfl | rfl | rfl)
        · exact subset_convexHull ℝ _ ⟨0, by simp⟩
        · exact subset_convexHull ℝ _
            ⟨⟨1, by omega⟩, by simp [tailCoeff, Nat.choose_eq_zero_of_lt hk1]⟩
        · exact subset_convexHull ℝ _ ⟨⟨oWt n k, by unfold oWt optWeight; omega⟩, by
            have : oWt n k ≠ 0 := (by unfold oWt optWeight; omega)
            simp [this, eAb, extremalAbscissa]⟩
    have hsc : S = {(1, 1), (eAb n k, 0), (0, 0)} := (by ext; simp [S, or_left_comm, or_comm]); have
      hodd (ho : Odd k) (p : ℝ × ℝ) : p ∈ aRg n k ρ ↔ 0 ≤ p.2 ∧ p.1 ≤ p.2 ∧ p.2 ≤ (p.1 - eAb n k) /
      (1 - eAb n k) := (by have := ext_odd (n := n) ho; rw [hch, hsc, tri_frac (by linarith)
                             (by norm_num) p, show (p.1 - 0) / (1 - 0) = p.1 by ring]); have hevn
      (he : Even k) (p : ℝ × ℝ) : p ∈ aRg n k ρ ↔ 0 ≤ p.2 ∧ (p.1 - eAb n k) / (1 - eAb n k) ≤ p.2 ∧
      p.2 ≤ p.1 := (by have := ext_evn (n := n) he; rw [hch, tri_frac (by linarith) (by linarith) p,
                         show (p.1 - 0) / (1 - 0) = p.1 by ring]); have hbd (p : ℝ × ℝ) (hp : p ∈
      aRg n k ρ) : 0 ≤ p.2 ∧ p.2 ≤ 1 := (by
      rcases Nat.even_or_odd k with he | ho; (· exact (by
        have := ext_evn (n := n) he; rw [hch, tri_hull (by linarith)] at hp; exact ⟨hp.1, hp.2.1⟩));
        (· exact (by have := ext_odd (n := n) ho; rw [hch, hsc, tri_hull (by linarith)] at hp; exact
                       ⟨hp.1, hp.2.1⟩))); have hid_att : MatrixMap.IsCompletelyPositive
      (LinearMap.id : QubitMap n) ∧ MatrixMap.IsTracePreserving (LinearMap.id : QubitMap n) ∧
      (realKFidelity ρ k (LinearMap.id : QubitMap n), realProcessFidelity (LinearMap.id : QubitMap
      n)) = (1, 1) := (by
      have hβ1 := hw_cLbl (n := n) (w := 1) (by omega); obtain ⟨hCP, hTP, hp⟩ := two_pCh k ρ hρ (β
        := cLbl n 1) (by omega) (t := 1) zero_le_one le_rfl q0 (by ext; simp [q0]); exact hid_eq ▸
        (⟨hCP, hTP, by simpa using hp⟩ : (pCh q0).IsCompletelyPositive ∧ (pCh q0).IsTracePreserving
        ∧ (realKFidelity ρ k (pCh q0), realProcessFidelity (pCh q0)) = (1, 1)))
    have hsng (β : PauliLabel n) (hβ : 1 ≤ hammingWeight β) : (pCh (fun γ => if γ = β then 1 else
      0)).IsCompletelyPositive ∧ (pCh (fun γ => if γ = β then 1 else 0)).IsTracePreserving ∧
      (realKFidelity ρ k (pCh (fun γ => if γ = β then 1 else 0)), realProcessFidelity (pCh (fun γ
      => if γ = β then 1 else 0))) = ((-1 : ℝ) ^ k * tCf k (hammingWeight β), 0) := by
      have hβ0 : β ≠ 0 := fun h => (by rw [h, hw_zero] at hβ; omega)
      obtain ⟨hCP, hTP, hp⟩ := two_pCh k ρ hρ hβ (t := 0) le_rfl zero_le_one
        (fun γ => if γ = β then 1 else 0) (by
          ext γ; by_cases h0 : γ = 0
          · subst h0; simp [hβ0.symm]
          · simp [h0])
      exact ⟨hCP, hTP, by simpa using hp⟩
    refine ⟨⟨hpos, hlt1⟩, hmax, hfilt, hch, hodd, hevn, hbd, hid_att, fun β hβ => ?_, ⟨cLbl n (oWt
      n k), hw_cLbl (Nat.min_le_left _ _)⟩, fun β hβ => ?_⟩
    · obtain ⟨hCP, hTP, hp⟩ := hsng β (by omega)
      exact ⟨hCP, hTP, by
        rw [hp, hβ, show tCf k 1 = 0 by simp [tailCoeff, Nat.choose_eq_zero_of_lt hk1]]; simp⟩
    · obtain ⟨hCP, hTP, hp⟩ := hsng β (by unfold optWeight at hβ; omega); exact
        ⟨hCP, hTP, by rw [hp, hβ]; rfl⟩
  · rintro ⟨hn1, hnk⟩; have hseg : convexHull ℝ ({(0, 0), (1, 1)} : Set (ℝ × ℝ)) = {p : ℝ × ℝ | p.1
      = p.2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} := (by
      rw [show ({(0, 0), (1, 1)} : Set (ℝ × ℝ)) = {(1, 1), (0, 0), (0, 0)} from
        (by ext; simp [or_comm]), tri_hull le_rfl]; ext p; dsimp; exact ⟨fun ⟨_, _, _, _⟩ =>
        ⟨by linarith, by linarith, by linarith⟩, fun ⟨_, _, _⟩ =>
        ⟨by linarith, by linarith, by linarith, by linarith⟩⟩)
    have hch : aRg n k ρ = convexHull ℝ ({(0, 0), (1, 1)} : Set (ℝ × ℝ)) := by
      rw [vImg_eq n k ρ hρ]; congr 1; ext p; simp only [Set.mem_range, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      refine ⟨fun ⟨i, hi⟩ => ?_, fun hp => ?_⟩
      · by_cases h0 : i.val = 0; (· simp [h0] at hi; exact Or.inr hi.symm); (· exact (by
          have hlt : i.val - 1 < k := (by have := i.isLt; omega); simp [h0, tCf, tailCoeff,
            Nat.choose_eq_zero_of_lt hlt] at hi; exact Or.inl hi.symm))
      · rcases hp with rfl | rfl
        · exact ⟨⟨1, by omega⟩, by simp [tailCoeff, Nat.choose_eq_zero_of_lt (by omega : 0 < k)]⟩
        · exact ⟨0, by simp⟩
    exact ⟨hch, hch.trans hseg⟩

theorem kFidelity_non_identifiability_of_processFidelity (n k : ℕ) (hn : 2 ≤ n) (hk : k + 1 ≤ n) (ρ
    : Fin n → Fin 4 → QubitMatrix) (hρ : ∀ i : Fin n, IsQubitSICProjector (ρ i)) : ∃ Λ₁ Λ₂ :
    QubitMap n, Λ₁.IsCompletelyPositive ∧ Λ₁.IsTracePreserving ∧ Λ₂.IsCompletelyPositive ∧
    Λ₂.IsTracePreserving ∧ realKFidelity ρ k Λ₁ = realKFidelity ρ k Λ₂ ∧ realProcessFidelity Λ₁ = 0
    ∧ 0 < realProcessFidelity Λ₂ ∧ realProcessFidelity Λ₁ ≠ realProcessFidelity Λ₂ := by
  suffices h : ∃ x y : ℝ, 0 < y ∧ (x, 0) ∈ achievableRegion n k ρ ∧
      (x, y) ∈ achievableRegion n k ρ by
    obtain ⟨x, y, hy0, ⟨Λ₁, hCP₁, hTP₁, he₁⟩, ⟨Λ₂, hCP₂, hTP₂, he₂⟩⟩ := h; have h1 := (congrArg
      Prod.snd he₁).symm; have h2 := (congrArg Prod.snd he₂).symm; dsimp at h1 h2; refine ⟨Λ₁, Λ₂,
      hCP₁, hTP₁, hCP₂, hTP₂,
      (by have hf1 := congrArg Prod.fst he₁; have hf2 := congrArg Prod.fst he₂; linarith), h1, h2 ▸
      hy0, (by rw [h1, h2]; exact ne_of_lt hy0)⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk1; (· exact (by
    have hiff := (achievableRegion_zero_characterization n (by omega) ρ hρ).2.1 hn; have :=
      pow3_le9 hn; let y : ℝ := ((3 : ℝ)⁻¹ - (3 : ℝ)⁻¹ ^ n) / (1 - (3 : ℝ)⁻¹ ^ n); have hy : 0 < y
      := div_pos (by linarith) (by linarith); exact ⟨(3 : ℝ)⁻¹, y, hy, (hiff _).mpr
      ⟨le_rfl, by norm_num, le_of_lt hy⟩, (hiff _).mpr ⟨le_of_lt hy, by linarith, le_rfl⟩⟩));
    (· exact (by
    obtain ⟨⟨hpos, hlt1⟩, _, _, hch, hodd, hevn, _⟩ :=
      (achievableRegion_intermediate_and_high_characterization n k ρ hρ).1 ⟨hk1, hk⟩; let x : ℝ :=
      eAb n k / 2; have hp₁ : (x, (0 : ℝ)) ∈ achievableRegion n k ρ := (by
      rw [hch, show (x, (0 : ℝ)) = (1 / 2 : ℝ) • ((0 : ℝ), (0 : ℝ)) + (1 / 2 : ℝ) • (eAb n k, (0 :
        ℝ)) from (by ext <;> dsimp [x] <;> ring)]; exact (convex_convexHull ℝ _) (subset_convexHull
        ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) (by norm_num) (by norm_num)
        (by norm_num)); rcases Nat.even_or_odd k with he | ho; (· exact (by
      have := ext_evn (n := n) he; have hxp : 0 < x := (by dsimp [x]; linarith); refine ⟨x, x, hxp,
        hp₁, (hevn he (x, x)).mpr ⟨le_of_lt hxp, ?_, le_rfl⟩⟩; have hneg := div_neg_of_neg_of_pos
        (by dsimp [x]; linarith : x - eAb n k < 0) (by linarith : 0 < 1 - eAb n k); linarith));
      (· exact (by
      have := ext_odd (n := n) ho; let y : ℝ := (x - eAb n k) / (1 - eAb n k); have hyp : 0 < y :=
        div_pos (by dsimp [x]; linarith) (by linarith); exact ⟨x, y, hyp, hp₁, (hodd ho (x, y)).mpr
        ⟨le_of_lt hyp, by dsimp [x]; linarith, le_rfl⟩⟩))))

end D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityAchievableRegion
