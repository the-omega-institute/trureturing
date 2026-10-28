/- GID: D5/S3/Entropy/GohGlibichukKonyagin/Result
   generality: G
   mirror-B: D5/B/S3/Entropy/GohGlibichukKonyagin/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Zero-atom laws refute the entropic Glibichuk–Konyagin conjecture for every k. -/


/-
admission_basis: open-problem-resolution (Refuted).
Utility none: all parameters range over arbitrary integers and prime fields; the proof
uses exact law identities and entropy inequalities, not finite certificates, bounded
enumeration, a checker, or a numerical reduction. Numerical examples are separate.
All declarations are bind-only under the inlining and normalization rule: finite sums
and the defining recurrence are normalized after the frozen entropy bracket, endpoint
characterizations and pinned Mathlib inequalities are instantiated. No escape witness
is claimed. Each helper has the consumers listed below; result settles the external claim.
Frozen dependency aliases (module GID; full Lean name; declaration statement_id):
F1 = D5/S3/Entropy/EntropyEquality; D5.S3.Entropy.EntropyEquality.entropy_eq_log_card_iff_uniform; sha256:71dc31bafc55792064ed900da5645d67f6ef2b67ee3f0c7fcc00ffe6ab609328
F2 = D5/S3/Entropy/EntropyEquality; D5.S3.Entropy.EntropyEquality.entropy_eq_zero_iff_point_mass; sha256:2dc204d16c2c0d7e7c1cb1e4bbe9dc83fc15662b52afde243e84caa99d732b78
F3 = D5/S3/Entropy/Forgetting/CapacityMonotone; D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward; sha256:cad2df6e983d5d173955b5b13a616de5ba6ba0334e17112c93d7f2ed629ffbca
F4 = D5/S3/Entropy/MaxEntropy; D5.S3.Entropy.MaxEntropy.entropy_le_log_card; sha256:2036c3d1e460f61aa9db5be6bee1f085a8eb400f9dccacc5244afc890263d5b5
F5 = D5/S3/Entropy/MaxEntropy; D5.S3.Entropy.MaxEntropy.shannonEntropy; sha256:0b9b0250c925b41ffab4b8ab0b198871ccb0bb46dd401760ec0158c98ad42e87
F6 = D5/S3/Entropy/Mixing/MixtureEntropyBracket; D5.S3.Entropy.Mixing.MixtureEntropyBracket.mixture; sha256:de4491d0ae630f3f9de49be09a957cd711faf07dabe23b952d49d1e728f507bc
F7 = D5/S3/Entropy/Mixing/MixtureEntropyBracket; D5.S3.Entropy.Mixing.MixtureEntropyBracket.mixture_entropy_le_weighted_add_weight_entropy; sha256:65bc3646947dcb71422dee98f8c1b1812cb0e5fe294aba5975f8119890bf8063
F8 = D5/S3/Entropy/Mixing/MixtureEntropyBracket; D5.S3.Entropy.Mixing.MixtureEntropyBracket.weighted_entropy_le_mixture_entropy; sha256:78261e59e58c1712aa1583739cca615f790f93f0f3b14775ecfdf1028ffa6688
M1 = Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution; DiscreteConvolution.addRingConvolution_apply; pinned upstream definition and fiber-sum API (consumed by conv_eq_sum)
Consumers below are authored declarations, computed from compiled type/value constants.
Private names are restored with privateToUserName; compiler auxiliaries are traversed
within each consumer, stopping at the next authored declaration. Generated self-use
and unused generated equations are not independent mathematical consumers.
Per-declaration judgment: name | proof_shape | frozen deps | escape_witness | consumers.
  delta | bind-only (definition) | none | none | spike,iterLaw,spike_sum,spike_law,spike_entropy,conv_spike,mul_spike,sum_spike
  spike | bind-only (definition) | none | none | spike_sum,spike_law,spike_entropy,conv_spike,mul_spike,sum_spike,violation,result
  conv | bind-only (definition) | M1 | none | conv_eq_sum,iterLaw,conv_spike,conv_mul,iter_product,sum_spike
  conv_eq_sum | bind-only | M1 | none | conv_spike,conv_mul
  mulLaw | bind-only (definition) | F3 | none | iterLaw,mul_spike,conv_mul,iter_product,sum_spike
  iterLaw | bind-only (definition) | F3,M1 | none | iter_product,sum_spike
  sumLaw | bind-only (definition) | F3 | none | claim,sum_spike,violation,result
  Hbits | bind-only (definition) | F5 | none | claim,violation,result
  claim | bind-only (definition) | F3,F5 | none | result
  card_pos | bind-only | none | none | spike_sum,spike_law,mul_spike,weight_bounds
  spike_sum | bind-only | none | none | spike_law,mul_spike
  spike_law | bind-only | none | none | result
  spike_entropy | bind-only | F1,F2,F4,F5,F6,F7,F8 | none | violation
  conv_spike | bind-only | M1 | none | sum_spike
  mul_spike | bind-only | F3 | none | sum_spike
  conv_mul | bind-only | F3,M1 | none | iter_product
  iter_product | bind-only | F3,M1 | none | sum_spike
  sum_spike | bind-only | F3,M1 | none | violation
  weight_bounds | bind-only | none | none | violation,result
  violation | bind-only | F1,F2,F3,F4,F5,F6,F7,F8,M1 | none | result
  result | bind-only | F1,F2,F3,F4,F5,F6,F7,F8,M1 | none | external Conjecture 15 settlement
Four-slot registration for violation and result is unfinished:
https://github.com/the-omega-institute/trureturing/issues/22907 .
Missing are lawful source selection and a source-bound realization bridge reconstructing
the full quantified strict inequality for violation and the negated existential/universal
claim for result, including primality, normalized laws and the independent pushforward;
also missing are the actual-positive law, variation, per-role sensitivity with the other
observations/anchors fixed, and actual observational dependence. The p-only Hbits readout
fails elaboration without Fact (Nat.Prime p); an explicit prime-subtype instance repairs
that readout but does not supply these family proofs. The source inspector rejects raw
dictionary/proof coordinates with unclassified_form:source.dictionary_or_proof_coordinate;
this is not a DTR verdict on a completed registration.
-/

import D5.S3.Entropy.Mixing.MixtureEntropyBracket
import D5.S3.Entropy.EntropyEquality
import D5.S3.Entropy.Forgetting.CapacityMonotone

/-! Exact zero-atom laws and entropy bounds for the entropic sum-product assertion. -/

namespace D5.S3.Entropy.GohGlibichukKonyagin.Result

open scoped BigOperators
open D5.S3.Entropy.MaxEntropy D5.S3.Entropy.Mixing.MixtureEntropyBracket
open D5.S3.Entropy.Forgetting.CapacityMonotone (pushforward)

noncomputable section

variable {p : ℕ} [Fact p.Prime]

private def delta (a : ZMod p) : ℝ := if a = 0 then 1 else 0
def spike (t : ℝ) (a : ZMod p) : ℝ := (1 - t) * delta a + t / p
private def conv (f g : ZMod p → ℝ) : ZMod p → ℝ :=
  DiscreteConvolution.addRingConvolution f g

private lemma conv_eq_sum (f g : ZMod p → ℝ) (z : ZMod p) :
    conv f g z = ∑ a, f a * g (z - a) := by
  let e : ZMod p ≃ DiscreteConvolution.addFiber z :=
    { toFun := fun a => ⟨(a, z - a), by simp [DiscreteConvolution.mem_addFiber]⟩
      invFun := fun ab => ab.1.1
      left_inv := by intro a; rfl
      right_inv := by
        intro ab
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have h := DiscreteConvolution.mem_addFiber.mp ab.property
          rw [sub_eq_iff_eq_add]
          simpa [add_comm] using h.symm }
  rw [conv, DiscreteConvolution.addRingConvolution_apply]
  rw [← e.tsum_eq]
  simp only [tsum_fintype]
  rfl
private def mulLaw (f : ZMod p → ℝ) : ZMod p → ℝ :=
  pushforward (fun a : ZMod p × ZMod p => a.1 * a.2) (fun a => f a.1 * f a.2)
private def iterLaw : ℕ → (ZMod p → ℝ) → ZMod p → ℝ
  | 0, _ => delta
  | n + 1, f => conv (mulLaw f) (iterLaw n f)
def sumLaw (n : ℕ) (f : ZMod p → ℝ) (z : ZMod p) : ℝ :=
  pushforward (fun v : (Fin n → ZMod p) × (Fin n → ZMod p) => ∑ i, v.1 i * v.2 i)
    (fun v => ∏ i, f (v.1 i) * f (v.2 i)) z

def Hbits (f : ZMod p → ℝ) : ℝ := shannonEntropy f / Real.log 2

def claim : Prop := ∃ k : ℕ, 3 ≤ k ∧ ∀ (p : ℕ) (_hp : p.Prime),
  letI : Fact p.Prime := ⟨_hp⟩
  ∀ μ : ZMod p → ℝ, (∀ a, 0 ≤ μ a) → (∑ a, μ a) = 1 →
    min (2 * Hbits μ) (Real.logb 2 p) - 1 ≤ Hbits (sumLaw k μ)

private lemma card_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos

private lemma spike_sum (t : ℝ) : (∑ a : ZMod p, spike t a) = 1 := by
  simp [spike, delta, Finset.sum_add_distrib, ZMod.card,
    ne_of_gt (card_pos (p := p)), mul_div_cancel₀]

private lemma spike_law {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∀ a : ZMod p, 0 ≤ spike t a) ∧ (∑ a : ZMod p, spike t a) = 1 := by
  refine ⟨?_, spike_sum t⟩
  intro a
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (by unfold delta; positivity))
    (div_nonneg ht card_pos.le)

private lemma spike_entropy {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t * Real.log p ≤ shannonEntropy (spike (p := p) t) ∧
    shannonEntropy (spike (p := p) t) ≤ Real.log 2 + t * Real.log p := by
  let w : Bool → ℝ := fun b => if b then t else 1 - t
  let q : Bool → ZMod p → ℝ := fun b => if b then (fun _ => (p : ℝ)⁻¹) else delta
  have hw : (∀ b, 0 ≤ w b) ∧ ∑ b, w b = 1 := by
    constructor
    · intro b; cases b <;> simp [w, ht, sub_nonneg.mpr ht1]
    · simp [w, Fintype.sum_bool]
  have hq : ∀ b, (∀ a, 0 ≤ q b a) ∧ ∑ a, q b a = 1 := by
    intro b; cases b
    · constructor
      · intro a; dsimp [q, delta]; positivity
      · simp [q, delta]
    · simp [q]
  have hm : mixture w q = spike (p := p) t := by
    ext a; simp [mixture, w, q, spike, Fintype.sum_bool, div_eq_mul_inv, add_comm]
  have hd : shannonEntropy (delta (p := p)) = 0 :=
    (D5.S3.Entropy.EntropyEquality.entropy_eq_zero_iff_point_mass delta
      ⟨fun a => by unfold delta; positivity, by simp [delta]⟩).mpr ⟨0, by ext a; simp [delta]⟩
  have hu : shannonEntropy (fun _ : ZMod p => (p : ℝ)⁻¹) = Real.log p := by
    simpa [ZMod.card] using
      (D5.S3.Entropy.EntropyEquality.entropy_eq_log_card_iff_uniform
        (fun _ : ZMod p => (p : ℝ)⁻¹) (hq true)).mpr (by simp [ZMod.card])
  have he : (∑ b, w b * shannonEntropy (q b)) = t * Real.log p := by
    simp [w, q, Fintype.sum_bool, hd, hu]
  have hlo := weighted_entropy_le_mixture_entropy w q hw hq
  have hhi := mixture_entropy_le_weighted_add_weight_entropy w q hw hq
  rw [hm, he] at hlo hhi
  have hwbound : shannonEntropy w ≤ Real.log 2 := by
    simpa only [Fintype.card_bool, Nat.cast_ofNat] using entropy_le_log_card w hw
  exact ⟨hlo, le_add_of_le_add_right hhi hwbound⟩

private lemma conv_spike (t u : ℝ) :
    conv (spike (p := p) t) (spike u) = spike (t + u - t * u) := by
  ext z
  rw [conv_eq_sum]
  simp only [spike, mul_add, add_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  simp [delta, sub_eq_zero, ZMod.card, ne_of_gt (card_pos (p := p))]
  <;> split_ifs <;> field_simp <;> ring

private lemma mul_spike (t : ℝ) :
    mulLaw (spike (p := p) t) = spike (t ^ 2 * (p - 1) / p) := by
  have hsum := spike_sum (p := p) t
  have inner (a z : ZMod p) (ha : a ≠ 0) :
      (∑ b, if a * b = z then spike t a * spike t b else 0) =
      spike t a * spike t (a⁻¹ * z) := by
    have he (b : ZMod p) : a * b = z ↔ b = a⁻¹ * z :=
      (eq_inv_mul_iff_mul_eq₀ ha).symm
    simp_rw [he]
    simp
  ext z
  rw [mulLaw, pushforward, Fintype.sum_prod_type, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
  simp only [zero_mul, ite_mul, mul_zero]
  have hrest : ∑ a ∈ Finset.univ.erase (0 : ZMod p), spike t a = (p - 1) * t / p := by
    have he : ∑ a ∈ Finset.univ.erase (0 : ZMod p), spike t a =
        ∑ a ∈ Finset.univ.erase (0 : ZMod p), t / p := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [spike, delta, (Finset.mem_erase.mp ha).1]
    rw [he]
    simp [ZMod.card, Nat.cast_sub (Fact.out : p.Prime).one_le]
    ring
  by_cases hz : z = 0
  · subst z
    simp only [ite_true]
    rw [show (∑ b, spike (p := p) t (0 : ZMod p) * spike t b) = spike (p := p) t (0 : ZMod p) by rw [← Finset.mul_sum, hsum, mul_one]]
    have he : (∑ a ∈ Finset.univ.erase (0 : ZMod p),
        ∑ b, if a * b = 0 then spike t a * spike t b else 0) =
        (∑ a ∈ Finset.univ.erase (0 : ZMod p), spike t a) * spike (p := p) t (0 : ZMod p) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [inner a 0 (Finset.mem_erase.mp ha).1, mul_zero]
    rw [he, hrest]
    simp [spike, delta]
    field_simp [ne_of_gt (card_pos (p := p))]
    <;> ring
  · simp only [Ne.symm hz, ite_false, Finset.sum_const_zero, add_zero]
    have he : (∑ a ∈ Finset.univ.erase (0 : ZMod p),
        ∑ b, if a * b = z then spike t a * spike t b else 0) =
        (∑ a ∈ Finset.univ.erase (0 : ZMod p), spike t a) * (t / p) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [inner a z (Finset.mem_erase.mp ha).1]
      simp [spike, delta, mul_ne_zero (inv_ne_zero (Finset.mem_erase.mp ha).1) hz]
    rw [he, hrest]
    simp [spike, delta, hz]
    ring

private lemma conv_mul (f g : ZMod p → ℝ) (z : ZMod p) :
    conv (mulLaw f) g z = ∑ a, ∑ b, f a * f b * g (z - a * b) := by
  rw [conv_eq_sum]
  simp only [mulLaw, pushforward, Fintype.sum_prod_type, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp

private lemma iter_product (n : ℕ) (f : ZMod p → ℝ) (z : ZMod p) :
    iterLaw n f z = ∑ v : Fin n → ZMod p × ZMod p,
      if (∑ i, (v i).1 * (v i).2) = z then ∏ i, f (v i).1 * f (v i).2 else 0 := by
  induction n generalizing z with
  | zero => simp [iterLaw, delta, eq_comm]
  | succ n ih =>
    rw [iterLaw, conv_mul]
    simp_rw [ih, Finset.mul_sum]
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ZMod p × ZMod p)).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, Fin.sum_univ_succ,
      Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro v _
    have he : (∑ i, (v i).1 * (v i).2) = z - a * b ↔
        a * b + ∑ i, (v i).1 * (v i).2 = z := eq_sub_iff_add_eq'
    simp only [he, mul_ite, mul_zero]

private lemma sum_spike (t : ℝ) (n : ℕ) :
    sumLaw n (spike (p := p) t) = spike (1 - (1 - t ^ 2 * (p - 1) / p) ^ n) := by
  have he : sumLaw n (spike (p := p) t) = iterLaw n (spike t) := by
    ext z
    unfold sumLaw pushforward
    rw [← (Equiv.arrowProdEquivProdArrow (Fin n)
      (fun _ => ZMod p) (fun _ => ZMod p)).sum_comp]
    rw [iter_product]
    apply Finset.sum_congr rfl
    intro v _
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_mk]
    split_ifs with h <;> simp_all
  rw [he]
  clear he
  induction n with
  | zero => ext a; simp [iterLaw, spike]
  | succ n ih =>
    rw [iterLaw, mul_spike t, ih, conv_spike]
    congr 1
    rw [pow_succ]
    ring
private lemma weight_bounds (k : ℕ) (hk : 3 ≤ k) :
    let s : ℝ := (1 / k) ^ 2 * (p - 1) / p
    let r : ℝ := 1 - (1 - s) ^ k
    0 ≤ (1 : ℝ) / k ∧ (1 : ℝ) / k ≤ 1 ∧
    0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ r ∧ r ≤ k * s ∧ k * s < 1 / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk : 0 < k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_of_lt hk : 1 ≤ k)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  dsimp
  have ht : 0 ≤ (1 : ℝ) / k := Nat.one_div_cast_nonneg k
  have ht1 : (1 : ℝ) / k ≤ 1 := (div_le_one hk0).mpr hk1
  have hs : 0 ≤ (1 / (k : ℝ)) ^ 2 * (p - 1) / p := by positivity
  have hks : (k : ℝ) * ((1 / k) ^ 2 * (p - 1) / p) < 1 / k := by
    calc
      _ = (1 / (k : ℝ)) * ((p - 1) / p) := by
        field_simp
        <;> ring
      _ < (1 / (k : ℝ)) * 1 :=
        mul_lt_mul_of_pos_left ((div_lt_one (card_pos (p := p))).mpr (by linarith))
          (one_div_pos.mpr hk0)
      _ = 1 / k := mul_one _
  have hs1 : (1 / (k : ℝ)) ^ 2 * (p - 1) / p ≤ 1 := by
    nlinarith
  have hb := one_add_mul_le_pow (a := -((1 / (k : ℝ)) ^ 2 * (p - 1) / p))
    (by linarith : (-2 : ℝ) ≤ -((1 / (k : ℝ)) ^ 2 * (p - 1) / p)) k
  simp only [← sub_eq_add_neg] at hb
  have hpw : (1 - (1 / (k : ℝ)) ^ 2 * (p - 1) / p) ^ k ≤ 1 :=
    pow_le_one₀ (sub_nonneg.mpr hs1) (sub_le_self 1 hs)
  exact ⟨ht, ht1, hs, hs1, sub_nonneg.mpr hpw, by linarith, hks⟩

theorem violation (k : ℕ) (hk : 3 ≤ k) (hp : 2 ^ (2 * k) < p) :
    Hbits (sumLaw k (spike (p := p) (1 / k))) <
      min (2 * Hbits (spike (p := p) (1 / k))) (Real.logb 2 p) - 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk : 0 < k)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_add_left_le hk : 2 ≤ k)
  obtain ⟨ht, ht1, hs, hs1, hr, hrs, hks⟩ := weight_bounds (p := p) k hk
  let s : ℝ := (1 / k) ^ 2 * (p - 1) / p
  let r : ℝ := 1 - (1 - s) ^ k
  have hr1 : r ≤ 1 / k := (le_trans hrs hks.le)
  have hrunit : r ≤ 1 := hr1.trans ht1
  have hlo := (spike_entropy (p := p) ht ht1).1
  have hhi := (spike_entropy (p := p) hr hrunit).2
  have hl0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (Fact.out : p.Prime).one_le)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl : 2 * k * Real.log 2 < Real.log p := by
    have he : (2 : ℝ) ^ (2 * k) < p := by exact_mod_cast hp
    have hh := Real.log_lt_log (by positivity) he
    simpa only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] using hh
  rw [sum_spike]
  change shannonEntropy (spike (p := p) r) / Real.log 2 < _
  have hm : 2 * (Real.log p / k / Real.log 2) ≤
      min (2 * Hbits (spike (p := p) (1 / k))) (Real.logb 2 p) := by
    apply le_min
    · unfold Hbits
      apply mul_le_mul_of_nonneg_left _ zero_le_two
      apply (div_le_div_iff_of_pos_right hl2).mpr
      simpa only [one_div, mul_comm, div_eq_mul_inv, mul_one] using hlo
    · rw [Real.logb, ← mul_div_assoc]
      apply (div_le_div_iff_of_pos_right hl2).mpr
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hk0).mpr
      nlinarith
  have hbound : shannonEntropy (spike (p := p) r) ≤ Real.log 2 + Real.log p / k := by
    calc
      _ ≤ Real.log 2 + r * Real.log p := hhi
      _ ≤ Real.log 2 + (1 / k) * Real.log p := by
        linarith [mul_le_mul_of_nonneg_right hr1 hl0]
      _ = _ := by ring
  have hgap : 2 * Real.log 2 < Real.log p / k := (lt_div_iff₀ hk0).mpr (by nlinarith)
  have hstrict : shannonEntropy (spike (p := p) r) / Real.log 2 <
      2 * (Real.log p / k / Real.log 2) - 1 := by
    apply (lt_sub_iff_add_lt).mpr
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ hl2).mpr
    rw [add_mul, div_mul_cancel₀ _ hl2.ne', one_mul]
    nlinarith
  exact hstrict.trans_le (sub_le_sub_right hm 1)

theorem result : ¬ claim := by
  rintro ⟨k, hk, hall⟩
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (2 ^ (2 * k) + 1)
  letI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨ht, ht1, _⟩ := weight_bounds (p := p) k hk
  have hlaw := spike_law (p := p) ht ht1
  exact (not_le_of_gt (violation k hk (Nat.lt_of_succ_le hp)))
    (hall p hprime (spike (1 / k)) hlaw.1 hlaw.2)

end
end D5.S3.Entropy.GohGlibichukKonyagin.Result
