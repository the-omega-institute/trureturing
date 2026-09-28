/- GID: D5/S3/Observer/MetricGeometry/ContractingDigitMemory
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/ContractingDigitMemory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contracting binary digit prefixes have an exact finite-state error law. -/

import D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open scoped BigOperators


namespace D5.S3.Observer.MetricGeometry.ContractingDigitMemory

open D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)

def bitVal (b : Bool) : ℝ := match b with | false => 0 | true => 1

noncomputable def digitValue (lam : ℝ) (b : ℕ → Bool) : ℝ :=
  (1 - lam) * ∑' j, bitVal (b j) * lam ^ j

private lemma digit_summable {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (b : ℕ → Bool) : Summable (fun j => bitVal (b j) * lam ^ j) := by
  refine Summable.of_nonneg_of_le (f := fun j => lam ^ j) (g := fun j => bitVal (b j) * lam ^ j)
      (fun j => by cases hb : b j <;> simp [bitVal, hb] <;> positivity)
      (fun j => by cases hb : b j <;> simp [bitVal, hb] <;> positivity)
      (summable_geometric_of_lt_one hlam hlam1)

lemma digitValue_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (b : ℕ → Bool) : 0 ≤ digitValue lam b := by
  unfold digitValue
  apply mul_nonneg (by linarith)
  exact tsum_nonneg (fun j => by
    cases hb : b j <;> simp [bitVal, hb] <;> positivity)

lemma digitValue_le_one {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (b : ℕ → Bool) : digitValue lam b ≤ 1 := by
  unfold digitValue
  have hsum := digit_summable hlam hlam1 b
  have hle : (∑' j, bitVal (b j) * lam ^ j) ≤ ∑' j, lam ^ j := by
    exact Summable.tsum_le_tsum
      (fun j => by cases hb : b j <;> simp [bitVal, hb] <;> positivity)
      hsum (summable_geometric_of_lt_one hlam hlam1)
  calc
    (1 - lam) * (∑' j, bitVal (b j) * lam ^ j) ≤
        (1 - lam) * ∑' j, lam ^ j :=
      mul_le_mul_of_nonneg_left hle (by linarith)
    _ = 1 := by rw [tsum_geometric_of_lt_one hlam hlam1]; exact (div_self (by linarith))

lemma digitValue_prefix {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (b : ℕ → Bool) (L : ℕ) :
    digitValue lam b =
      (1 - lam) * (∑ j ∈ Finset.range L, bitVal (b j) * lam ^ j) +
        lam ^ L * digitValue lam (fun i => b (i + L)) := by
  unfold digitValue
  rw [← Summable.sum_add_tsum_nat_add L (digit_summable hlam hlam1 b)]
  calc
    (1 - lam) * (∑ i ∈ Finset.range L, bitVal (b i) * lam ^ i +
        ∑' i, bitVal (b (i + L)) * lam ^ (i + L)) =
        (1 - lam) * (∑ i ∈ Finset.range L, bitVal (b i) * lam ^ i) +
          (1 - lam) * ∑' i, bitVal (b (i + L)) * lam ^ (i + L) := by ring
    _ = (1 - lam) * (∑ i ∈ Finset.range L, bitVal (b i) * lam ^ i) +
          lam ^ L * ((1 - lam) * ∑' i, bitVal (b (i + L)) * lam ^ i) := by
      have hshift :
          (1 - lam) * ∑' i, bitVal (b (i + L)) * lam ^ (i + L) =
            lam ^ L * ((1 - lam) * ∑' i, bitVal (b (i + L)) * lam ^ i) := by
        calc
          (1 - lam) * ∑' i, bitVal (b (i + L)) * lam ^ (i + L) =
              ∑' i, (1 - lam) * (bitVal (b (i + L)) * lam ^ (i + L)) :=
                (tsum_mul_left).symm
          _ = ∑' i, lam ^ L * ((1 - lam) * (bitVal (b (i + L)) * lam ^ i)) := by
            apply tsum_congr
            intro i
            simp only [pow_add]
            ring
          _ = lam ^ L * ((1 - lam) * ∑' i, bitVal (b (i + L)) * lam ^ i) := by
            rw [tsum_mul_left, tsum_mul_left]
      rw [hshift]

def prepend (a : Bool) (b : ℕ → Bool) : ℕ → Bool
  | 0 => a
  | n + 1 => b n

lemma digitValue_prepend {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (a : Bool) (b : ℕ → Bool) :
    digitValue lam (prepend a b) = (1 - lam) * bitVal a + lam * digitValue lam b := by
  rw [digitValue_prefix hlam hlam1 (prepend a b) 1]
  simp [prepend, digitValue]

lemma digitValue_zero_tail {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (b : ℕ → Bool) (L : ℕ) :
    digitValue lam (fun j => if h : j < L then b j else false) =
      (1 - lam) * (∑ j ∈ Finset.range L, bitVal (b j) * lam ^ j) := by
  rw [digitValue_prefix hlam hlam1 _ L]
  have hzero : digitValue lam (fun i => if h : i + L < L then b (i + L) else false) = 0 := by
    unfold digitValue
    simp only [show ∀ i : ℕ, ¬ i + L < L by omega]
    simp [bitVal]
  rw [hzero, mul_zero, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  simp [hj]

lemma digitValue_close_of_prefix {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (b c : ℕ → Bool) (L : ℕ) (hbc : ∀ j < L, b j = c j) :
    |digitValue lam b - digitValue lam c| ≤ lam ^ L := by
  rw [digitValue_prefix hlam hlam1 b L, digitValue_prefix hlam hlam1 c L]
  have hsum : (∑ j ∈ Finset.range L, bitVal (b j) * lam ^ j) =
      ∑ j ∈ Finset.range L, bitVal (c j) * lam ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [hbc j hj]
  rw [hsum]
  have htail : |digitValue lam (fun i => b (i + L)) -
      digitValue lam (fun i => c (i + L))| ≤ 1 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [digitValue_nonneg hlam hlam1 (fun i => b (i + L)),
      digitValue_le_one hlam hlam1 (fun i => b (i + L)),
      digitValue_nonneg hlam hlam1 (fun i => c (i + L)),
      digitValue_le_one hlam hlam1 (fun i => c (i + L))]
  calc
    |(1 - lam) * (∑ j ∈ Finset.range L, bitVal (c j) * lam ^ j) +
          lam ^ L * digitValue lam (fun i => b (i + L)) -
        ((1 - lam) * (∑ j ∈ Finset.range L, bitVal (c j) * lam ^ j) +
          lam ^ L * digitValue lam (fun i => c (i + L)))| =
      |lam ^ L * (digitValue lam (fun i => b (i + L)) -
          digitValue lam (fun i => c (i + L)))| := by ring_nf
    _ = lam ^ L * |digitValue lam (fun i => b (i + L)) -
          digitValue lam (fun i => c (i + L))| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hlam L)]
    _ ≤ lam ^ L * 1 := mul_le_mul_of_nonneg_left htail (pow_nonneg hlam L)
    _ = lam ^ L := by ring

lemma digitValue_interval_of_prefix {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (b c : ℕ → Bool) (L : ℕ) (hbc : ∀ j < L, b j = c j)
    (hczero : ∀ i, c (i + L) = false) :
    digitValue lam c ≤ digitValue lam b ∧
      digitValue lam b ≤ digitValue lam c + lam ^ L := by
  rw [digitValue_prefix hlam hlam1 b L, digitValue_prefix hlam hlam1 c L]
  have hsum : (∑ j ∈ Finset.range L, bitVal (b j) * lam ^ j) =
      ∑ j ∈ Finset.range L, bitVal (c j) * lam ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [hbc j hj]
  rw [hsum]
  have hb0 := digitValue_nonneg hlam hlam1 (fun i => b (i + L))
  have hb1 := digitValue_le_one hlam hlam1 (fun i => b (i + L))
  have hc : digitValue lam (fun i => c (i + L)) = 0 := by
    unfold digitValue
    simp [hczero, bitVal]
  have hpow : 0 ≤ lam ^ L := pow_nonneg hlam L
  have hleft : 0 ≤ lam ^ L * digitValue lam (fun i => b (i + L)) :=
    mul_nonneg hpow hb0
  have hright : lam ^ L * digitValue lam (fun i => b (i + L)) ≤ lam ^ L :=
    (mul_le_mul_of_nonneg_left hb1 hpow).trans_eq (by ring)
  have hcp : lam ^ L * digitValue lam (fun i => c (i + L)) = 0 := by
    rw [hc, mul_zero]
  rw [hcp]
  constructor <;> nlinarith

def digitK (lam : ℝ) : Set ℝ := Set.range (digitValue lam)

abbrev DigitState (lam : ℝ) := {x : ℝ // x ∈ digitK lam}

noncomputable def digitStep (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (a : Bool) (x : DigitState lam) : DigitState lam :=
  ⟨(1 - lam) * bitVal a + lam * x.1, by
    rcases x.2 with ⟨b, hb⟩
    refine ⟨prepend a b, ?_⟩
    rw [← hb, digitValue_prepend hlam hlam1 a b]⟩

def prefixStream (L : ℕ) (u : Fin L → Bool) : ℕ → Bool :=
  fun j => if h : j < L then u ⟨j, h⟩ else false

noncomputable def prefixPoint (lam : ℝ) (L : ℕ) (u : Fin L → Bool) : ℝ :=
  digitValue lam (prefixStream L u)

noncomputable def prefixClass (lam : ℝ) (L : ℕ) (u : Fin L → Bool) : Set (DigitState lam) :=
  {x | ∃ b : ℕ → Bool, x.1 = digitValue lam b ∧
      ∀ (j : ℕ) (hj : j < L), b j = u ⟨j, hj⟩}

lemma prefixPoint_mem (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (L : ℕ) (u : Fin L → Bool) :
    (⟨prefixPoint lam L u, ⟨prefixStream L u, rfl⟩⟩ : DigitState lam) ∈
      prefixClass lam L u := by
  refine ⟨prefixStream L u, rfl, ?_⟩
  intro j hj
  simp [prefixStream, hj]

lemma prefix_class_covers (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (L : ℕ) (x : DigitState lam) :
    ∃ u : Fin L → Bool, x ∈ prefixClass lam L u := by
  rcases x.2 with ⟨b, hb⟩
  let u : Fin L → Bool := fun j => b j.1
  refine ⟨u, ?_⟩
  refine ⟨b, hb.symm, ?_⟩
  intro j hj
  rfl

lemma prefix_class_step (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (L : ℕ) (a : Bool) (u : Fin L → Bool) :
    Set.MapsTo (digitStep lam hlam hlam1 a) (prefixClass lam L u)
      (prefixClass lam L (fun i => if i.1 = 0 then a else u ⟨i.1 - 1, by omega⟩)) := by
  intro x hx
  rcases hx with ⟨b, hb, hprefix⟩
  refine ⟨prepend a b, ?_, ?_⟩
  · change (digitStep lam hlam hlam1 a x).1 = digitValue lam (prepend a b)
    simp [digitStep, hb, digitValue_prepend hlam hlam1]
  · intro j hj
    by_cases hj0 : j = 0
    · subst j; simp [prepend]
    · have hj1 : 0 < j := Nat.pos_of_ne_zero hj0
      cases j with
      | zero => omega
      | succ n => simpa [prepend] using hprefix n (by omega)

lemma prefix_class_radius (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (L : ℕ) (u : Fin L → Bool) :
    ∀ x : DigitState lam, x ∈ prefixClass lam L u →
      dist x.1 (prefixPoint lam L u) ≤ lam ^ L := by
  intro x hx
  rcases hx with ⟨b, hb, hprefix⟩
  have h := digitValue_close_of_prefix hlam hlam1 b (prefixStream L u) L (by
    intro j hj
    rw [hprefix j hj]
    simp [prefixStream, hj])
  simpa [Real.dist_eq, prefixPoint, hb] using h

lemma geometric_weight {lam : ℝ} (L : ℕ) :
    (1 - lam) * (∑ j ∈ Finset.range L, lam ^ j) = 1 - lam ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ, pow_succ]
      calc
        (1 - lam) * (∑ x ∈ Finset.range L, lam ^ x + lam ^ L) =
            (1 - lam) * (∑ x ∈ Finset.range L, lam ^ x) +
              (1 - lam) * lam ^ L := by ring
        _ = 1 - lam ^ L + (1 - lam) * lam ^ L := by rw [ih]
        _ = 1 - lam ^ (L + 1) := by ring

lemma prefixPoint_upper {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (L : ℕ) (u : Fin L → Bool) :
    0 ≤ prefixPoint lam L u ∧ prefixPoint lam L u ≤ 1 - lam ^ L := by
  constructor
  · exact digitValue_nonneg hlam hlam1 _
  · unfold prefixPoint
    rw [digitValue_prefix hlam hlam1 (prefixStream L u) L]
    have hzero : digitValue lam (fun i => prefixStream L u (i + L)) = 0 := by
      unfold digitValue
      simp only [prefixStream, show ∀ i : ℕ, ¬ i + L < L by omega]
      simp [bitVal]
    rw [hzero, mul_zero, add_zero]
    have hsum : (∑ j ∈ Finset.range L,
        bitVal (prefixStream L u j) * lam ^ j) ≤
        ∑ j ∈ Finset.range L, lam ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases h : j < L
      · cases hu : u ⟨j, h⟩ <;> simp [bitVal, prefixStream, h, hu] <;> positivity
      · exact False.elim (h (Finset.mem_range.mp hj))
    calc
      (1 - lam) * (∑ j ∈ Finset.range L,
          bitVal (prefixStream L u j) * lam ^ j) ≤
          (1 - lam) * (∑ j ∈ Finset.range L, lam ^ j) :=
        mul_le_mul_of_nonneg_left hsum (by linarith)
      _ = 1 - lam ^ L := geometric_weight L

lemma prefixPoint_succ {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (n : ℕ) (u : Fin (n + 1) → Bool) :
    prefixPoint lam (n + 1) u =
      (1 - lam) * bitVal (u 0) +
        lam * prefixPoint lam n (fun i => u i.succ) := by
  have hstream : prefixStream (n + 1) u =
      prepend (u 0) (prefixStream n (fun i => u i.succ)) := by
    funext j
    cases j with
    | zero => simp [prefixStream, prepend]
    | succ j =>
      by_cases hj : j < n
      · simp [prefixStream, prepend, hj]
      · have hj' : ¬j + 1 < n + 1 := by omega
        simp [prefixStream, prepend, hj, hj']
  rw [prefixPoint, hstream, digitValue_prepend hlam hlam1]
  rfl

lemma prefixPoint_separated {lam : ℝ} (hlam : 0 ≤ lam) (hlamhalf : lam < 1 / 2)
    : ∀ n : ℕ, ∀ u v : Fin n → Bool, u ≠ v →
      (1 - lam) * lam ^ (n - 1) ≤ |prefixPoint lam n u - prefixPoint lam n v| := by
  intro n
  induction n with
  | zero =>
      intro u v huv
      exfalso
      apply huv
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      intro u v huv
      by_cases hhead : u 0 = v 0
      · let ut : Fin n → Bool := fun i => u i.succ
        let vt : Fin n → Bool := fun i => v i.succ
        have htail : ut ≠ vt := by
          intro h
          apply huv
          funext i
          refine Fin.cases hhead ?_ i
          intro j
          exact congrFun h j
        rw [prefixPoint_succ hlam (by linarith) n u,
          prefixPoint_succ hlam (by linarith) n v, hhead]
        have hi := ih ut vt htail
        dsimp [ut, vt] at hi ⊢
        have hnonneg : 0 ≤ lam := hlam
        have hrewrite :
            ((1 - lam) * bitVal (v 0) + lam * prefixPoint lam n ut) -
              ((1 - lam) * bitVal (v 0) + lam * prefixPoint lam n vt) =
              lam * (prefixPoint lam n ut - prefixPoint lam n vt) := by ring
        rw [hrewrite, abs_mul, abs_of_nonneg hnonneg]
        calc
          lam * |prefixPoint lam n ut - prefixPoint lam n vt| ≥
              lam * ((1 - lam) * lam ^ (n - 1)) :=
            mul_le_mul_of_nonneg_left hi hnonneg
          _ = (1 - lam) * lam ^ ((n + 1) - 1) := by
            have hn : 1 ≤ n := by
              by_contra hn
              have : n = 0 := by omega
              subst n
              exact htail (funext (fun i => Fin.elim0 i))
            rw [Nat.add_sub_cancel]
            calc
              lam * ((1 - lam) * lam ^ (n - 1)) =
                  (1 - lam) * (lam ^ (n - 1) * lam) := by ring
              _ = (1 - lam) * lam ^ n := by
                rw [← pow_succ, Nat.sub_add_cancel hn]
      · have hbits : u 0 = false ∧ v 0 = true ∨ u 0 = true ∧ v 0 = false := by
          cases hu : u 0 <;> cases hv : v 0 <;> simp_all
        rcases hbits with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · rw [prefixPoint_succ hlam (by linarith) n u,
            prefixPoint_succ hlam (by linarith) n v, hu, hv]
          rcases prefixPoint_upper hlam (by linarith) n (fun i => u i.succ) with ⟨hu0, huR⟩
          rcases prefixPoint_upper hlam (by linarith) n (fun i => v i.succ) with ⟨hv0, hvR⟩
          simp [bitVal] at *
          have hV : 0 ≤ lam * prefixPoint lam n (fun i => v i.succ) :=
            mul_nonneg hlam hv0
          have hU : lam * prefixPoint lam n (fun i => u i.succ) ≤
              lam * (1 - lam ^ n) :=
            mul_le_mul_of_nonneg_left huR hlam
          have hdiff : (1 - lam) * lam ^ n ≤
              (1 - lam) + lam * prefixPoint lam n (fun i => v i.succ) -
                lam * prefixPoint lam n (fun i => u i.succ) := by
            nlinarith
          have hbase : 0 ≤ (1 - lam) * lam ^ n :=
            mul_nonneg (by linarith) (pow_nonneg hlam n)
          have hnonpos :
              lam * prefixPoint lam n (fun i => u i.succ) -
                ((1 - lam) + lam * prefixPoint lam n (fun i => v i.succ)) ≤ 0 := by
            nlinarith
          rw [abs_of_nonpos hnonpos]
          simpa [Nat.add_sub_cancel] using hdiff

        · rw [prefixPoint_succ hlam (by linarith) n u,
            prefixPoint_succ hlam (by linarith) n v, hu, hv]
          rcases prefixPoint_upper hlam (by linarith) n (fun i => u i.succ) with ⟨hu0, huR⟩
          rcases prefixPoint_upper hlam (by linarith) n (fun i => v i.succ) with ⟨hv0, hvR⟩
          simp [bitVal] at *
          have hU : 0 ≤ lam * prefixPoint lam n (fun i => u i.succ) :=
            mul_nonneg hlam hu0
          have hV : lam * prefixPoint lam n (fun i => v i.succ) ≤
              lam * (1 - lam ^ n) :=
            mul_le_mul_of_nonneg_left hvR hlam
          have hdiff : (1 - lam) * lam ^ n ≤
              (1 - lam) + lam * prefixPoint lam n (fun i => u i.succ) -
                lam * prefixPoint lam n (fun i => v i.succ) := by
            nlinarith
          have hbase : 0 ≤ (1 - lam) * lam ^ n :=
            mul_nonneg (by linarith) (pow_nonneg hlam n)
          have hnonpos :
              0 ≤ (1 - lam) + lam * prefixPoint lam n (fun i => u i.succ) -
                lam * prefixPoint lam n (fun i => v i.succ) := by
            nlinarith
          rw [abs_of_nonneg hnonpos]
          simpa [Nat.add_sub_cancel] using hdiff

theorem contracting_digit_memory_exact
    {lam eps : ℝ} (hlampos : 0 < lam) (hlamhalf : lam < 1 / 2)
    (L : ℕ) (hL : 1 ≤ L)
    (heps_lower : lam ^ L / 2 ≤ eps)
    (heps_upper : eps < (1 - lam) * lam ^ (L - 1) / 2) :
    IsLeast
      {s : ℕ |
        HasFinitePredictor
          (digitStep lam hlampos.le (by linarith))
          (fun x : DigitState lam => x.1) eps s}
      (2 ^ L) := by
  let hstep : Bool → DigitState lam → DigitState lam :=
    digitStep lam hlampos.le (by linarith)
  let hreadout : DigitState lam → ℝ := fun x => x.1
  have heps : 0 ≤ eps := le_trans (by positivity) heps_lower
  have hcard : Fintype.card (Fin L → Bool) = 2 ^ L := by
    simp [Fintype.card_fun]
  have hupper : HasFiniteInvariantCover
      (hstep) hreadout eps (2 ^ L) := by
    let δ : Bool → (Fin L → Bool) → (Fin L → Bool) := fun a u i =>
      if i.1 = 0 then a else u ⟨i.1 - 1, by omega⟩
    let y : (Fin L → Bool) → ℝ := fun u =>
      prefixPoint lam L u + lam ^ L / 2
    refine ⟨Fin L → Bool, inferInstance, ?_, ?_, prefixClass lam L, δ, y, ?_⟩
    · exact ⟨fun _ => false⟩
    · simpa [hcard]
    · refine {
        nonempty := fun u => ⟨_, prefixPoint_mem lam hlampos.le (by linarith) L u⟩
        covers := fun x => prefix_class_covers lam hlampos.le (by linarith) L x
        successor := ?_
        radius := ?_ }
      · intro a u
        simpa [δ] using prefix_class_step lam hlampos.le (by linarith) L a u
      · intro u
        apply iSup_le
        rintro ⟨x, hx⟩
        apply (edist_le_ofReal heps).2
        rcases hx with ⟨b, hb, hprefix⟩
        have hinter := digitValue_interval_of_prefix hlampos.le (by linarith)
          b (prefixStream L u) L (by
            intro j hj
            rw [hprefix j hj]
            simp [prefixStream, hj]) (by
              intro i
              simp [prefixStream])
        have hdist : dist x.1 (y u) ≤ lam ^ L / 2 := by
          rw [Real.dist_eq]
          rw [hb]
          simp only [y, prefixPoint]
          have hmid : 0 ≤ lam ^ L := by positivity
          rw [abs_le]
          constructor <;> linarith
        exact hdist.trans heps_lower
  letI : Nonempty (DigitState lam) :=
    ⟨⟨prefixPoint lam L (fun _ => false),
      ⟨prefixStream L (fun _ => false), rfl⟩⟩⟩
  have hiff := (finite_predictor_iff_forward_invariant_cover
      hstep hreadout eps heps (2 ^ L)
      (Nat.one_le_pow L 2 (by omega))).1
  constructor
  · exact hiff.mpr hupper
  · intro s hs
    rcases hs with ⟨S, finiteS, hne, hScard, e, G, h, herr⟩
    letI : Fintype S := finiteS
    let z : (Fin L → Bool) → DigitState lam := fun u =>
      ⟨prefixPoint lam L u, ⟨prefixStream L u, rfl⟩⟩
    have hz_injective : Function.Injective (fun u => e (z u)) := by
      intro u v huv
      by_contra huv'
      have hsep := prefixPoint_separated hlampos.le hlamhalf L u v huv'
      have huerr : dist (h (e (z u))) (z u).1 ≤ eps := by
        simpa [hstep, hreadout, z, runWord] using herr (z u) []
      have hverr : dist (h (e (z v))) (z v).1 ≤ eps := by
        simpa [hstep, hreadout, z, runWord] using herr (z v) []
      have hsame : h (e (z u)) = h (e (z v)) := congrArg h huv
      have hdist : dist (z u).1 (z v).1 ≤ 2 * eps := by
        calc
          dist (z u).1 (z v).1 ≤
              dist (z u).1 (h (e (z u))) + dist (h (e (z v))) (z v).1 := by
                rw [hsame]
                exact dist_triangle _ _ _
          _ ≤ eps + eps := add_le_add (by simpa [dist_comm] using huerr) hverr
          _ = 2 * eps := by ring
      have hsep' : (1 - lam) * lam ^ (L - 1) ≤ 2 * eps := by
        simpa [z, Real.dist_eq, abs_sub_comm] using le_trans hsep hdist
      linarith
    have hcard_le : Fintype.card (Fin L → Bool) ≤ Fintype.card S :=
      Fintype.card_le_of_injective (fun u => e (z u)) hz_injective
    simpa [hcard] using le_trans hcard_le hScard

example {lam : ℝ} (hlampos : 0 < lam) (hlamhalf : lam < 1 / 2)
    (L : ℕ) (hL : 1 ≤ L) :
    IsLeast
      {s : ℕ |
        HasFinitePredictor
          (digitStep lam hlampos.le (by linarith))
          (fun x : DigitState lam => x.1) (lam ^ L / 2) s}
      (2 ^ L) := by
  apply contracting_digit_memory_exact hlampos hlamhalf L hL le_rfl
  have hpow : lam ^ L = lam ^ (L - 1) * lam := by
    calc
      lam ^ L = lam ^ (L - 1 + 1) := by
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega))]
      _ = lam ^ (L - 1) * lam := by rw [pow_succ']; ring
  have hpowpos : 0 < lam ^ (L - 1) := pow_pos hlampos (L - 1)
  rw [hpow]
  nlinarith



end D5.S3.Observer.MetricGeometry.ContractingDigitMemory
