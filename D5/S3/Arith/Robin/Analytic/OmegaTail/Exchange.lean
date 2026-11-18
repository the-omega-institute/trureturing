/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/Exchange
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/Exchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed paired prime exchanges and fixed-grid lower counts. -/

import D5.S3.Arith.Robin.Analytic.OmegaTail.Entropy
import D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Fintype.Pi

/-! Signed prime exchanges on a common base and their application to paired grid bins. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (primeInterval)

private lemma mem_selected_union {J : Type*} [Fintype J]
    {P f : J → Finset ℕ} (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hf : ∀ j, f j ⊆ P j) {j : J} {p : ℕ} (hp : p ∈ P j) :
    p ∈ univ.biUnion f ↔ p ∈ f j := by
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp h
    by_cases hij : i = j
    · simpa [hij] using hi
    · exact ((disjoint_left.mp (hd hij)) (hf i hi) hp).elim
  · intro h
    exact mem_biUnion.mpr ⟨j, mem_univ _, h⟩

/-- On one prime base, removing and adding the same prescribed number in
each paired bin realizes the full independent product of choices. -/
theorem paired_exchange {J : Type*} [Fintype J]
    (base : Finset ℕ) (D R : J → Finset ℕ) (h : J → ℕ)
    (lo hi : J → ℝ) (x : ℝ)
    (hbase : ∀ p ∈ base, Nat.Prime p)
    (hD : ∀ j, D j ⊆ base) (hR : ∀ j, Disjoint (R j) base)
    (hDdisj : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hRdisj : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hprime : ∀ j, ∀ p ∈ R j, Nat.Prime p)
    (hlo : ∀ j, ∀ p ∈ D j, lo j ≤ log (p : ℝ))
    (hhi : ∀ j, ∀ p ∈ R j, log (p : ℝ) ≤ hi j)
    (hx : 0 < x)
    (hslack : (∑ p ∈ base, log (p : ℝ)) + ∑ j, (h j : ℝ) * (hi j - lo j) < log x) :
    ∃ outputs : Finset ℕ,
      outputs.card = (∏ j, (D j).card.choose (h j) * (R j).card.choose (h j)) ∧
      ∀ n ∈ outputs, 0 < n ∧ Squarefree n ∧ ArithmeticFunction.cardDistinctFactors n =
        base.card ∧ (n : ℝ) < x := by
  classical
  let C := Fintype.piFinset (fun j => (D j).powersetCard (h j)) ×ˢ
    Fintype.piFinset (fun j => (R j).powersetCard (h j))
  let removed := fun f : (J → Finset ℕ) × (J → Finset ℕ) => univ.biUnion f.1
  let added := fun f : (J → Finset ℕ) × (J → Finset ℕ) => univ.biUnion f.2
  let support := fun f => (base \ removed f) ∪ added f
  let output := fun f => ∏ p ∈ support f, p
  have hdf {f} (hf : f ∈ C) (j : J) : f.1 j ⊆ D j ∧ (f.1 j).card = h j :=
    mem_powersetCard.mp (Fintype.mem_piFinset.mp (mem_product.mp hf).1 j)
  have hrf {f} (hf : f ∈ C) (j : J) : f.2 j ⊆ R j ∧ (f.2 j).card = h j :=
    mem_powersetCard.mp (Fintype.mem_piFinset.mp (mem_product.mp hf).2 j)
  have hrem {f} (hf : f ∈ C) : removed f ⊆ base := by
    intro p hp
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp hp
    exact hD j ((hdf hf j).1 hj)
  have hadd {f} (hf : f ∈ C) : Disjoint (added f) base := by
    apply disjoint_left.mpr
    intro p hp hb
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp hp
    exact disjoint_left.mp (hR j) ((hrf hf j).1 hj) hb
  have hunion {f} (hf : f ∈ C) : Disjoint (base \ removed f) (added f) :=
    (hadd hf).symm.mono_left sdiff_subset
  have hDpair {f} (hf : f ∈ C) : ((univ : Finset J) : Set J).PairwiseDisjoint f.1 :=
    fun i _ j _ hij => (hDdisj hij).mono (hdf hf i).1 (hdf hf j).1
  have hRpair {f} (hf : f ∈ C) : ((univ : Finset J) : Set J).PairwiseDisjoint f.2 :=
    fun i _ j _ hij => (hRdisj hij).mono (hrf hf i).1 (hrf hf j).1
  have hsupport {f} (hf : f ∈ C) : ∀ p ∈ support f, Nat.Prime p := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact hbase p (mem_sdiff.mp hp).1
    · obtain ⟨j, _, hj⟩ := mem_biUnion.mp hp
      exact hprime j p ((hrf hf j).1 hj)
  have hrecover {f} (hf : f ∈ C) (j : J) :
      D j \ support f = f.1 j ∧ support f ∩ R j = f.2 j := by
    constructor
    · ext p
      constructor
      · intro hp
        obtain ⟨hd, hs⟩ := mem_sdiff.mp hp
        apply (mem_selected_union hDdisj (fun j => (hdf hf j).1) hd).mp
        exact not_not.mp fun hm => hs (mem_union_left _ (mem_sdiff.mpr ⟨hD j hd, hm⟩))
      · intro hp
        have hd := (hdf hf j).1 hp
        refine mem_sdiff.mpr ⟨hd, ?_⟩
        intro hs
        rcases mem_union.mp hs with hs | hs
        · exact (mem_sdiff.mp hs).2
            ((mem_selected_union hDdisj (fun j => (hdf hf j).1) hd).mpr hp)
        · exact disjoint_left.mp (hadd hf) hs (hD j hd)
    · ext p
      constructor
      · intro hp
        obtain ⟨hs, hr⟩ := mem_inter.mp hp
        apply (mem_selected_union hRdisj (fun j => (hrf hf j).1) hr).mp
        rcases mem_union.mp hs with hs | hs
        · exact (disjoint_left.mp (hR j) hr (mem_sdiff.mp hs).1).elim
        · exact hs
      · intro hp
        have hr := (hrf hf j).1 hp
        exact mem_inter.mpr ⟨mem_union_right _
          ((mem_selected_union hRdisj (fun j => (hrf hf j).1) hr).mpr hp), hr⟩
  have hinj : Set.InjOn output (C : Set ((J → Finset ℕ) × (J → Finset ℕ))) := by
    intro f hf g hg he
    have hs : support f = support g := by
      simpa only [output, Nat.primeFactors_prod (hsupport hf),
        Nat.primeFactors_prod (hsupport hg)] using congrArg Nat.primeFactors he
    exact Prod.ext (funext fun j => by rw [← (hrecover hf j).1, hs, (hrecover hg j).1])
      (funext fun j => by rw [← (hrecover hf j).2, hs, (hrecover hg j).2])
  refine ⟨C.image output, ?_, ?_⟩
  · simp only [card_image_of_injOn hinj, C, card_product, Fintype.card_piFinset,
      card_powersetCard, prod_mul_distrib]
  · intro n hn
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hn
    have hcard : (support f).card = base.card := by
      have hDcard : (removed f).card = ∑ j, h j := by
        rw [show removed f = univ.biUnion f.1 from rfl, card_biUnion (hDpair hf)]
        exact sum_congr rfl fun j _ => (hdf hf j).2
      have hRcard : (added f).card = ∑ j, h j := by
        rw [show added f = univ.biUnion f.2 from rfl, card_biUnion (hRpair hf)]
        exact sum_congr rfl fun j _ => (hrf hf j).2
      rw [show support f = (base \ removed f) ∪ added f from rfl,
        card_union_of_disjoint (hunion hf), card_sdiff_of_subset (hrem hf),
        hRcard, ← hDcard, Nat.sub_add_cancel (card_le_card (hrem hf))]
    have hlog :
        log (output f : ℝ) = (∑ p ∈ base, log (p : ℝ)) -
          (∑ j, ∑ p ∈ f.1 j, log (p : ℝ)) + (∑ j, ∑ p ∈ f.2 j, log (p : ℝ)) := by
      dsimp only [output]
      rw [Nat.cast_prod, log_prod (fun p hp => by exact_mod_cast (hsupport hf p hp).ne_zero)]
      dsimp only [support]
      rw [sum_union (hunion hf), sum_sdiff_eq_sub (hrem hf)]
      simp only [removed, added, sum_biUnion (hDpair hf), sum_biUnion (hRpair hf)]
    have hdonor : (∑ j, (h j : ℝ) * lo j) ≤ ∑ j, ∑ p ∈ f.1 j, log (p : ℝ) := by
      apply sum_le_sum
      intro j _
      calc
        (h j : ℝ) * lo j = ∑ _p ∈ f.1 j, lo j := by simp [(hdf hf j).2]
        _ ≤ _ := sum_le_sum fun p hp => hlo j p ((hdf hf j).1 hp)
    have hrecipient : (∑ j, ∑ p ∈ f.2 j, log (p : ℝ)) ≤ ∑ j, (h j : ℝ) * hi j := by
      apply sum_le_sum
      intro j _
      calc
        (∑ p ∈ f.2 j, log (p : ℝ)) ≤ ∑ _p ∈ f.2 j, hi j :=
          sum_le_sum fun p hp => hhi j p ((hrf hf j).1 hp)
        _ = _ := by simp [(hrf hf j).2]
    have hnpos : 0 < output f := prod_pos fun p hp => (hsupport hf p hp).pos
    refine ⟨hnpos, ?_, ?_, (log_lt_log_iff (by exact_mod_cast hnpos) hx).mp ?_⟩
    · apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro p hp q hq hpq
        exact (Nat.irreducible_iff_nat_prime p).mpr (hsupport hf p hp) |>.isRelPrime_iff_not_dvd.mpr
          (fun hd => hpq ((Nat.prime_dvd_prime_iff_eq (hsupport hf p hp)
            (hsupport hf q hq)).mp hd))
      · exact fun p hp => (hsupport hf p hp).squarefree
    · rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
        Nat.toFinset_factors, show output f = ∏ p ∈ support f, p from rfl,
        Nat.primeFactors_prod (hsupport hf), hcard]
    · rw [hlog]
      simp only [mul_sub, sum_sub_distrib] at hslack
      linarith


/-- Primes in the half-open grid bin below the centre. -/
def donorBin {m : ℕ} (t : Fin (m + 1) → ℝ) (P s : ℝ) (i : Fin m) : Finset ℕ :=
  primeInterval (P * exp (-t i.succ / s)) (P * exp (-t i.castSucc / s))

/-- Primes in the paired half-open grid bin above the centre. -/
def recipientBin {m : ℕ} (t : Fin (m + 1) → ℝ) (P s : ℝ) (i : Fin m) : Finset ℕ :=
  primeInterval (P * exp (t i.castSucc / s)) (P * exp (t i.succ / s))

private lemma primeInterval_endpoints {a b : ℝ} {p : ℕ} (hb : 0 ≤ b)
    (hp : p ∈ primeInterval a b) : a < (p : ℝ) ∧ (p : ℝ) ≤ b ∧ Nat.Prime p := by
  have h := mem_filter.mp hp
  have hi := mem_Ioc.mp h.1
  exact ⟨Nat.lt_of_floor_lt hi.1, (Nat.le_floor_iff hb).mp hi.2, h.2⟩

/-- The paired exponential grid contributes both choices in each bin to the
second-threshold tail, provided the pointwise exchange cost fits the reserve. -/
theorem fixed_grid_bound {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : StrictMono t)
    (ht0 : t 0 = 0) (P s reserve : ℝ) (hP : 0 < P) (hs : 0 < s)
    (base : Finset ℕ) (h : Fin m → ℕ)
    (hbase : base ⊆ Nat.primesLE ⌊P⌋₊)
    (hdonor : ∀ i, donorBin t P s i ⊆ base)
    (lambda : ℝ) (hsize : threshold lambda (exp P) < (base.card : ℝ))
    (hreserve : (∑ p ∈ base, log (p : ℝ)) ≤ P - reserve)
    (hcost : (2 / s) * (∑ i, t i.succ * (h i : ℝ)) < reserve) :
    (∏ i, (donorBin t P s i).card.choose (h i) *
      (recipientBin t P s i).card.choose (h i)) ≤ tailCount lambda (exp P) := by
  let L : Fin (m + 1) → ℝ := fun i => P * exp (-t i / s)
  let U : Fin (m + 1) → ℝ := fun i => P * exp (t i / s)
  have hLp (i) : 0 < L i := mul_pos hP (exp_pos _)
  have hUp (i) : 0 < U i := mul_pos hP (exp_pos _)
  have hL : StrictAnti L := by
    intro i j hij
    exact mul_lt_mul_of_pos_left (exp_lt_exp.mpr
      (div_lt_div_of_pos_right (neg_lt_neg (ht hij)) hs)) hP
  have hU : StrictMono U := by
    intro i j hij
    exact mul_lt_mul_of_pos_left (exp_lt_exp.mpr
      (div_lt_div_of_pos_right (ht hij) hs)) hP
  have hbelow (i : Fin m) {p} (hp : p ∈ donorBin t P s i) :=
    primeInterval_endpoints (hLp i.castSucc).le hp
  have habove (i : Fin m) {p} (hp : p ∈ recipientBin t P s i) :=
    primeInterval_endpoints (hUp i.succ).le hp
  have hdd : Pairwise (fun i j => Disjoint (donorBin t P s i) (donorBin t P s j)) := by
    have step (i j : Fin m) (hij : i < j) :
        Disjoint (donorBin t P s i) (donorBin t P s j) := by
      apply disjoint_left.mpr
      intro p hpi hpj
      exact ((hbelow i hpi).1.not_ge)
        ((hbelow j hpj).2.1.trans (hL.antitone (Fin.succ_le_castSucc_iff.mpr hij)))
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact step i j h
    · exact (step j i h).symm
  have hrd : Pairwise (fun i j => Disjoint (recipientBin t P s i) (recipientBin t P s j)) := by
    have step (i j : Fin m) (hij : i < j) :
        Disjoint (recipientBin t P s i) (recipientBin t P s j) := by
      apply disjoint_left.mpr
      intro p hpi hpj
      exact ((habove j hpj).1.not_ge)
        ((habove i hpi).2.1.trans (hU.monotone (Fin.succ_le_castSucc_iff.mpr hij)))
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact step i j h
    · exact (step j i h).symm
  have hrbase (i : Fin m) : Disjoint (recipientBin t P s i) base := by
    apply disjoint_left.mpr
    intro p hp hb
    have hU0 : U 0 = P := by simp [U, ht0]
    have hbound : (p : ℝ) ≤ P :=
      (Nat.le_floor_iff hP.le).mp (Nat.mem_primesLE.mp (hbase hb)).1
    have hcentre : P ≤ U i.castSucc := hU0 ▸ hU.monotone (Fin.zero_le i.castSucc)
    exact (habove i hp).1.not_ge (hbound.trans hcentre)
  have hexchange := paired_exchange base (donorBin t P s) (recipientBin t P s) h
    (fun i => log P - t i.succ / s) (fun i => log P + t i.succ / s) (exp P)
    (fun p hp => (Nat.mem_primesLE.mp (hbase hp)).2)
    hdonor hrbase hdd hrd (fun i _ hp => (habove i hp).2.2) ?_ ?_ (exp_pos P) ?_
  · obtain ⟨outputs, hcard, hout⟩ := hexchange
    rw [← hcard, tailCount]
    apply card_le_card
    intro n hn
    obtain ⟨hnpos, _, hω, hstrict⟩ := hout n hn
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hnpos, ?_⟩, ?_⟩
    · exact (Nat.le_floor_iff (exp_pos P).le).mpr hstrict.le
    · simpa only [hω] using hsize
  · intro i p hp
    have h := log_le_log (hLp i.succ) (hbelow i hp).1.le
    rwa [show log (L i.succ) = log P - t i.succ / s by
      rw [show L i.succ = P * exp (-t i.succ / s) from rfl,
        log_mul hP.ne' (exp_pos _).ne', log_exp, neg_div, sub_eq_add_neg]] at h
  · intro i p hp
    have h := log_le_log (by exact_mod_cast (habove i hp).2.2.pos) (habove i hp).2.1
    rwa [show log (U i.succ) = log P + t i.succ / s by
      rw [show U i.succ = P * exp (t i.succ / s) from rfl,
        log_mul hP.ne' (exp_pos _).ne', log_exp]] at h
  · rw [log_exp]
    have hsum : (∑ i, (h i : ℝ) * ((log P + t i.succ / s) - (log P - t i.succ / s))) =
        (2 / s) * (∑ i, t i.succ * (h i : ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    rw [hsum]
    linarith


/-- Fixed-grid entropy bound with the moving-bin capacities and safe-base
estimates as inputs. The floor, signed slack, full product count, and
conversion to the source scale are derived within the proof. -/
theorem fixed_grid_lower_of_capacity {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : StrictMono t)
    (ht0 : t 0 = 0) (q : Fin m → ℝ) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (eta : ℝ) (heta : 0 < eta) (base : ℝ → Finset ℕ) (reserve : ℝ → ℝ)
    (zeta : ℝ) (hzeta : 0 < zeta) :
    let c := π / (2 * sqrt 3)
    let C := (1 + eta) * c
    let s := fun P : ℝ => C * sqrt (log P)
    let W := fun P : ℝ => (P / log P) / s P
    let Z := fun P : ℝ => (P / log P) / sqrt (log P)
    let delta := fun i : Fin m => t i.succ - t i.castSucc
    (2 * ∑ i, t i.succ * (delta i * q i) < (π ^ 2 / 6) * (1 + eta) ^ 2) →
    (∀ i, Tendsto (fun P => ((donorBin t P (s P) i).card : ℝ) / W P) atTop (𝓝 (delta i))) →
    (∀ i, Tendsto (fun P => ((recipientBin t P (s P) i).card : ℝ) / W P) atTop (𝓝 (delta i))) →
    (Tendsto (fun P => reserve P / (W P / s P)) atTop (𝓝 ((π ^ 2 / 6) * (1 + eta) ^ 2))) →
    (∀ᶠ P in atTop, base P ⊆ Nat.primesLE ⌊P⌋₊ ∧
      (∀ i, donorBin t P (s P) i ⊆ base P) ∧
      (base P).card = Selection.selectedCount 1 (exp P) ∧
      (∑ p ∈ base P, log (p : ℝ)) ≤ P - reserve P) →
    ∀ᶠ P in atTop,
      ((2 * ∑ i, delta i * binEntropy (q i)) / C - zeta) * Z P ≤
        log (tailCount 1 (exp P) : ℝ) := by
  intro c C s W Z delta hslack hd hr hreserve hbase
  have hC : 0 < C := mul_pos (by linarith) (div_pos pi_pos (by positivity))
  have hdelta (i : Fin m) : 0 < delta i := sub_pos.mpr (ht i.castSucc_lt_succ)
  have hZ : Tendsto Z atTop atTop := by
    apply ((tendsto_exp_div_rpow_atTop (3 / 2 : ℝ)).comp tendsto_log_atTop).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    have hl := log_pos hP
    change exp (log P) / log P ^ (3 / 2 : ℝ) = (P / log P) / sqrt (log P)
    rw [exp_log (zero_lt_one.trans hP), div_div, sqrt_eq_rpow,
      show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      rpow_add hl, rpow_one]
  have hW : Tendsto W atTop atTop := by
    apply (hZ.atTop_div_const hC).congr'
    exact Eventually.of_forall fun P => by
      change ((P / log P) / sqrt (log P)) / C = (P / log P) / (C * sqrt (log P))
      rw [div_div, mul_comm (sqrt (log P)) C]
  let M (i : Fin m) (P : ℝ) :=
    min (donorBin t P (s P) i).card (recipientBin t P (s P) i).card
  let h (i : Fin m) (P : ℝ) := ⌊q i * (M i P : ℝ)⌋₊
  have hδM (i : Fin m) : Tendsto (fun P => (M i P : ℝ) / W P) atTop (𝓝 (delta i)) := by
    have hmin := (hd i).min (hr i)
    rw [min_self] at hmin
    apply hmin.congr'
    filter_upwards [hW.eventually_gt_atTop 0] with P hWP
    simp only [M, Nat.cast_min, min_div_div_right hWP.le]
  have hh (i : Fin m) : Tendsto (fun P => (h i P : ℝ) / W P) atTop
      (𝓝 (delta i * q i)) := by
    have hM : Tendsto (fun P => (M i P : ℝ)) atTop atTop := by
      apply (hW.atTop_mul_pos (hdelta i) (hδM i)).congr'
      filter_upwards [hW.eventually_gt_atTop 0] with P hWP
      exact mul_div_cancel₀ _ hWP.ne'
    have hf := ((tendsto_nat_floor_mul_div_atTop (hq0 i).le).comp hM).mul (hδM i)
    rw [mul_comm (q i) (delta i)] at hf
    apply hf.congr'
    filter_upwards [hM.eventually_gt_atTop 0] with P hMP
    change (h i P : ℝ) / (M i P : ℝ) * ((M i P : ℝ) / W P) = _
    rw [div_mul_div_cancel₀ hMP.ne']
  have hfit (i : Fin m) (P : ℝ) : h i P ≤ M i P := by
    have hm : (0 : ℝ) ≤ M i P := Nat.cast_nonneg _
    exact (Nat.floor_le_of_le (by nlinarith [mul_nonneg (sub_nonneg.mpr (hq1 i).le) hm]))
  have hnormalized :
      Tendsto (fun P => 2 * ∑ i, t i.succ * ((h i P : ℝ) / W P)) atTop
        (𝓝 (2 * ∑ i, t i.succ * (delta i * q i))) :=
    (tendsto_finsetSum univ (fun i _ => (hh i).const_mul (t i.succ))).const_mul 2
  have hbudget := hnormalized.eventually_lt hreserve hslack
  have hrl (i : Fin m) : 0 < delta i * q i := mul_pos (hdelta i) (hq0 i)
  have hru (i : Fin m) : delta i * q i < delta i :=
    mul_lt_of_lt_one_right (hdelta i) (hq1 i)
  have hentropy := tendsto_finsetSum univ (fun i _ =>
    ((Entropy.log_choose_scaled W (fun P => (donorBin t P (s P) i).card) (h i)
      hW (hdelta i) (hrl i) (hru i) (hd i) (hh i)).add
    (Entropy.log_choose_scaled W (fun P => (recipientBin t P (s P) i).card) (h i)
      hW (hdelta i) (hrl i) (hru i) (hr i) (hh i))))
  have heq (i : Fin m) : delta i * q i / delta i = q i :=
    mul_div_cancel_left₀ _ (hdelta i).ne'
  simp only [heq, ← two_mul, ← mul_sum] at hentropy
  have hlow := hentropy.eventually_const_lt
    (sub_lt_self (2 * ∑ i, delta i * binEntropy (q i)) (mul_pos hzeta hC))
  filter_upwards [hbudget, hlow, hbase, hW.eventually_gt_atTop 0, eventually_gt_atTop 1]
    with P hbudgetP hlowP hbaseP hWP hP
  have hsP : 0 < s P := mul_pos hC (sqrt_pos.2 (log_pos hP))
  have hcost : (2 / s P) * (∑ i, t i.succ * (h i P : ℝ)) < reserve P := by
    have hh := (lt_div_iff₀ (div_pos hWP hsP)).mp hbudgetP
    convert hh using 1
    simp only [mul_assoc, sum_mul, mul_sum]
    apply sum_congr rfl
    intro i _
    field_simp [hsP.ne', hWP.ne']
    <;> ring
  have hsize : threshold 1 (exp P) < ((base P).card : ℝ) := by
    rw [hbaseP.2.2.1, Selection.selectedCount, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  have hcount := fixed_grid_bound t ht ht0 P (s P) (reserve P) (zero_lt_one.trans hP) hsP
    (base P) (fun i => h i P) hbaseP.1 hbaseP.2.1 1 hsize hbaseP.2.2.2 hcost
  let d : Fin m → ℕ := fun i => (donorBin t P (s P) i).card.choose (h i P)
  let r : Fin m → ℕ := fun i => (recipientBin t P (s P) i).card.choose (h i P)
  have hdp (i : Fin m) : (0 : ℝ) < d i := by
    dsimp [d]
    exact_mod_cast Nat.choose_pos ((hfit i P).trans (min_le_left _ _))
  have hrp (i : Fin m) : (0 : ℝ) < r i := by
    dsimp [r]
    exact_mod_cast Nat.choose_pos ((hfit i P).trans (min_le_right _ _))
  have hprod : (0 : ℝ) < ((∏ i, d i * r i : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    simp only [Nat.cast_mul]
    exact prod_pos fun i _ => mul_pos (hdp i) (hrp i)
  have hlog := log_le_log hprod (show ((∏ i, d i * r i : ℕ) : ℝ) ≤
      (tailCount 1 (exp P) : ℝ) by exact_mod_cast hcount)
  rw [Nat.cast_prod, log_prod (fun i _ => by
    simpa only [Nat.cast_mul] using (mul_pos (hdp i) (hrp i)).ne')] at hlog
  simp only [Nat.cast_mul, log_mul (hdp _).ne' (hrp _).ne'] at hlog
  have hsum : (2 * ∑ i, delta i * binEntropy (q i)) - zeta * C <
      (∑ i, (log (d i : ℝ) + log (r i : ℝ))) / W P := by
    rw [sum_div]
    simp only [add_div]
    exact hlowP
  refine le_trans (le_of_lt ?_) hlog
  have hscale : Z P = C * W P := by
    change (P / log P) / sqrt (log P) = C * ((P / log P) / (C * sqrt (log P)))
    field_simp [hC.ne', (sqrt_pos.2 (log_pos hP)).ne']
  rw [hscale, ← mul_assoc, sub_mul, div_mul_cancel₀ _ hC.ne']
  exact (lt_div_iff₀ hWP).mp hsum

end D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange
