/- GID: D5/S3/Combinatorics/NumericalSemigroup/SignedResidueRelation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NumericalSemigroup/SignedResidueRelation
   mirror-E: none(waiver:general-signed-residue-relation)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Signed residue collisions give bounded relations on the original generators. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Tactic

/-! Finite signed residue arithmetic and its genuine reduced toric relation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation
open scoped BigOperators

/-- Total positive mass of an integer vector. -/
def positiveMass {e : ℕ} (v : Fin e → ℤ) : ℕ := ∑ i, (v i).toNat

/-- Total negative mass of the same integer vector. -/
def negativeMass {e : ℕ} (v : Fin e → ℤ) : ℕ := ∑ i, (-v i).toNat

/-- The finite signed vectors with both masses at most q. -/
def signedVectors (e q : ℕ) : Finset (Fin e → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ => Finset.Icc (-(q : ℤ)) q).filter
    (fun v => positiveMass v ≤ q ∧ negativeMass v ≤ q)

private theorem mem_signedVectors_iff (e q : ℕ) (v : Fin e → ℤ) :
    v ∈ signedVectors e q ↔ positiveMass v ≤ q ∧ negativeMass v ≤ q := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    have hp : (v i).toNat ≤ positiveMass v :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (v j).toNat) (Finset.mem_univ i)
    have hn : (-v i).toNat ≤ negativeMass v :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (-v j).toNat) (Finset.mem_univ i)
    apply Finset.mem_Icc.mpr
    omega

private def consEmbedding (e : ℕ) (a : ℕ ↪ ℤ) :
    (Σ _ : ℕ, Fin e → ℤ) ↪ (Fin (e + 1) → ℤ) where
  toFun z := Fin.cons (a z.1) z.2
  inj' := by
    rintro ⟨k, v⟩ ⟨l, w⟩ h
    have hk : k = l := a.injective (congrFun h 0)
    subst l
    have hv : v = w := funext fun i => congrFun h i.succ
    subst w
    rfl

private def positiveHead : ℕ ↪ ℤ :=
  ⟨fun k => (k : ℤ) + 1, by intro k l h; dsimp at h; omega⟩

private def negativeHead : ℕ ↪ ℤ :=
  ⟨fun k => -((k : ℤ) + 1), by intro k l h; dsimp at h; omega⟩

/-- Full-support vectors, constructed by choosing a nonzero first coordinate and
    allocating its mass from the corresponding one of two separate budgets. -/
private def fullVectors : (e p n : ℕ) → Finset (Fin e → ℤ)
  | 0, _, _ => {Fin.elim0}
  | e + 1, p, n =>
      (((Finset.range p).sigma fun k => fullVectors e (p - 1 - k) n).map
        (consEmbedding e positiveHead)) ∪
      (((Finset.range n).sigma fun k => fullVectors e p (n - 1 - k)).map
        (consEmbedding e negativeHead))

private theorem fullVectors_mass (e p n : ℕ) (v : Fin e → ℤ)
    (hv : v ∈ fullVectors e p n) : positiveMass v ≤ p ∧ negativeMass v ≤ n := by
  induction e generalizing p n with
  | zero => simp [positiveMass, negativeMass]
  | succ e ih =>
    rw [fullVectors, Finset.mem_union] at hv
    rcases hv with hv | hv
    · obtain ⟨⟨k, w⟩, hkw, rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨hk, hw⟩ := Finset.mem_sigma.mp hkw
      have h := ih _ _ w hw
      have hk' := Finset.mem_range.mp hk
      change positiveMass (Fin.cons ((k : ℤ) + 1) w) ≤ p ∧
        negativeMass (Fin.cons ((k : ℤ) + 1) w) ≤ n
      simp only [positiveMass, negativeMass, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ] at *
      have hp : ((k : ℤ) + 1).toNat = k + 1 := by omega
      have hn : (-((k : ℤ) + 1)).toNat = 0 := by omega
      rw [hp, hn]
      omega
    · obtain ⟨⟨k, w⟩, hkw, rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨hk, hw⟩ := Finset.mem_sigma.mp hkw
      have h := ih _ _ w hw
      have hk' := Finset.mem_range.mp hk
      change positiveMass (Fin.cons (-((k : ℤ) + 1)) w) ≤ p ∧
        negativeMass (Fin.cons (-((k : ℤ) + 1)) w) ≤ n
      simp only [positiveMass, negativeMass, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ, neg_neg] at *
      have hp : (-((k : ℤ) + 1)).toNat = 0 := by omega
      have hn : ((k : ℤ) + 1).toNat = k + 1 := by omega
      rw [hp, hn]
      omega

private theorem fullVectors_card_succ (e p n : ℕ) :
    (fullVectors (e + 1) p n).card =
      (∑ k ∈ Finset.range p, (fullVectors e (p - 1 - k) n).card) +
      ∑ k ∈ Finset.range n, (fullVectors e p (n - 1 - k)).card := by
  rw [fullVectors, Finset.card_union_of_disjoint]
  · simp only [Finset.card_map, Finset.card_sigma]
  · apply Finset.disjoint_left.mpr
    intro v hp hn
    obtain ⟨⟨k, w⟩, _, hk⟩ := Finset.mem_map.mp hp
    obtain ⟨⟨l, z⟩, _, hl⟩ := Finset.mem_map.mp hn
    have h := congrFun (hk.trans hl.symm) 0
    change (k : ℤ) + 1 = -((l : ℤ) + 1) at h
    omega

private theorem sum_choose_below (p i : ℕ) :
    (∑ k ∈ Finset.range p, (p - 1 - k).choose i) = p.choose (i + 1) := by
  rw [Finset.sum_range_reflect (fun k => k.choose i) p]
  cases p with
  | zero => simp
  | succ p =>
    rw [← Nat.sum_Icc_choose p i]
    symm
    apply Finset.sum_subset
    · intro k hk
      have hk' := Finset.mem_Icc.mp hk
      exact Finset.mem_range.mpr (by omega)
    · intro k hk hnot
      have hk' := Finset.mem_range.mp hk
      apply Nat.choose_eq_zero_of_lt
      by_contra hn
      apply hnot
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

private theorem fullVectors_card (e p n : ℕ) :
    (fullVectors e p n).card =
      ∑ i ∈ Finset.range (e + 1), e.choose i * p.choose i * n.choose (e - i) := by
  induction e generalizing p n with
  | zero => simp [fullVectors]
  | succ e ih =>
    rw [fullVectors_card_succ]
    simp_rw [ih]
    rw [Finset.sum_comm (s := Finset.range p), Finset.sum_comm (s := Finset.range n)]
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum, sum_choose_below]
    have hs : (∑ i ∈ Finset.range (e + 2), (e + 1).choose i *
        (p.choose i * n.choose (e + 1 - i))) =
        (∑ i ∈ Finset.range (e + 1), e.choose i * (p.choose i * n.choose (e + 1 - i))) +
        ∑ i ∈ Finset.range (e + 1), e.choose i * (p.choose (i + 1) * n.choose (e - i)) :=
      Finset.sum_choose_succ_mul (R := ℕ) (fun i j => p.choose i * n.choose j) e
    rw [show e + 1 + 1 = e + 2 by omega,
      show (∑ i ∈ Finset.range (e + 2), (e + 1).choose i * p.choose i *
        n.choose (e + 1 - i)) =
        ∑ i ∈ Finset.range (e + 2), (e + 1).choose i *
          (p.choose i * n.choose (e + 1 - i)) by simp_rw [mul_assoc],
      hs]
    rw [add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ e := by simpa using hi
      rw [show e + 1 - i = e - i + 1 by omega]
      ring
    · apply Finset.sum_congr rfl
      intro i _
      ring

/-- The disjoint full-support sign families give the registered binomial lower bound. -/
theorem signed_count_lower_bound (e q : ℕ) :
    (∑ i ∈ Finset.range (e + 1), e.choose i * q.choose i * q.choose (e - i)) ≤
      (signedVectors e q).card := by
  rw [← fullVectors_card e q q]
  apply Finset.card_le_card
  intro v hv
  exact (mem_signedVectors_iff e q v).mpr (fullVectors_mass e q q v hv)

private theorem central_coefficient_gap (e : ℕ) (he : 3 ≤ e) :
    8 ^ e < e.centralBinom * 3 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num [Nat.centralBinom, Nat.choose]
  | succ e he ih =>
    have h : (e + 1) * 8 ^ (e + 1) <
        (e + 1) * ((e + 1).centralBinom * 3 ^ (e + 1)) := by
      calc
      (e + 1) * 8 ^ (e + 1) = (8 * (e + 1)) * 8 ^ e := by ring
      _ < (8 * (e + 1)) * (e.centralBinom * 3 ^ e) :=
        Nat.mul_lt_mul_of_pos_left ih (by omega)
      _ ≤ (6 * (2 * e + 1)) * (e.centralBinom * 3 ^ e) := by
        exact Nat.mul_le_mul_right _ (by omega : 8 * (e + 1) ≤ 6 * (2 * e + 1))
      _ = (e + 1) * ((e + 1).centralBinom * 3 ^ (e + 1)) := by
        rw [show (e + 1) * ((e + 1).centralBinom * 3 ^ (e + 1)) =
          ((e + 1) * (e + 1).centralBinom) * 3 ^ (e + 1) by ring,
          Nat.succ_mul_centralBinom_succ, pow_succ]
        ring
    exact (Nat.mul_lt_mul_left (by omega : 0 < e + 1)).mp h

private theorem choose_scaled_limit (k : ℕ) (a : ℕ → ℕ) (c : ℝ)
    (ha : Filter.Tendsto a Filter.atTop Filter.atTop)
    (hc : Filter.Tendsto (fun r => (a r : ℝ) / r) Filter.atTop (nhds c)) :
    Filter.Tendsto (fun r => (Nat.choose (a r) k : ℝ) / (r : ℝ) ^ k)
      Filter.atTop (nhds (c ^ k / k.factorial)) := by
  have heq := ((isEquivalent_choose k).comp_tendsto ha).div
    (Asymptotics.IsEquivalent.refl (u := fun r : ℕ => (r : ℝ) ^ k))
  apply heq.symm.tendsto_nhds
  convert (hc.pow k).div_const (k.factorial : ℝ) using 1
  funext r
  simp only [Pi.div_apply, Function.comp_apply, div_pow]
  ring

private theorem mass_scale_limit :
    Filter.Tendsto (fun r : ℕ => ((3 * r / 8 : ℕ) : ℝ) / r)
      Filter.atTop (nhds (3 / 8 : ℝ)) := by
  let err : ℕ → ℝ := fun r => (3 * (r : ℝ)) / 8 - (3 * r / 8 : ℕ)
  have herr (r : ℕ) : 0 ≤ err r ∧ err r ≤ 1 := by
    have hlo : 8 * (3 * r / 8) ≤ 3 * r := Nat.mul_div_le (3 * r) 8
    have hhi : 3 * r < 8 * (3 * r / 8 + 1) := by omega
    have hlo' : (8 : ℝ) * (3 * r / 8 : ℕ) ≤ 3 * (r : ℝ) := by exact_mod_cast hlo
    have hhi' : 3 * (r : ℝ) < 8 * ((3 * r / 8 : ℕ) + 1 : ℝ) := by exact_mod_cast hhi
    dsimp [err]
    constructor <;> linarith
  have hz : Filter.Tendsto (fun r : ℕ => err r / r) Filter.atTop (nhds 0) :=
    tendsto_bdd_div_atTop_nhds_zero (Filter.Eventually.of_forall fun r => (herr r).1)
      (Filter.Eventually.of_forall fun r => (herr r).2) tendsto_natCast_atTop_atTop
  have h : Filter.Tendsto (fun r : ℕ => (3 / 8 : ℝ) - err r / r)
      Filter.atTop (nhds (3 / 8 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub hz :
      Filter.Tendsto (fun r : ℕ => (3 / 8 : ℝ) - err r / r) _ (nhds (3 / 8 - 0)))
  apply Filter.Tendsto.congr' _ h
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with r hr
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  dsimp [err]
  field_simp [hr']
  ring

private theorem mass_scale_atTop :
    Filter.Tendsto (fun r : ℕ => 3 * r / 8) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro n
  filter_upwards [Filter.eventually_ge_atTop (8 * (n + 1))] with r hr
  omega

private theorem lower_coefficient (e : ℕ) (c : ℝ) :
    (∑ i ∈ Finset.range (e + 1), (e.choose i : ℝ) *
      (c ^ i / i.factorial) * (c ^ (e - i) / (e - i).factorial)) =
      (e.centralBinom : ℝ) * c ^ e / e.factorial := by
  have hterm (i : ℕ) (hi : i ∈ Finset.range (e + 1)) :
      (e.choose i : ℝ) * (c ^ i / i.factorial) * (c ^ (e - i) / (e - i).factorial) =
        (e.choose i : ℝ) ^ 2 * c ^ e / e.factorial := by
    have hi' : i ≤ e := by simpa using hi
    calc
      _ = (e.choose i : ℝ) * (c ^ i * c ^ (e - i)) /
          ((i.factorial : ℝ) * (e - i).factorial) := by ring
      _ = (e.choose i : ℝ) * c ^ e /
          ((i.factorial : ℝ) * (e - i).factorial) := by
        rw [← pow_add, Nat.add_sub_of_le hi']
      _ = _ := by
        rw [Nat.cast_choose ℝ hi']
        field_simp
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_div, ← Finset.sum_mul]
  congr 2
  exact_mod_cast Nat.sum_range_choose_sq e

private theorem lower_count_limit (e : ℕ) :
    Filter.Tendsto (fun r : ℕ =>
      ((∑ i ∈ Finset.range (e + 1), e.choose i * (3 * r / 8).choose i *
        (3 * r / 8).choose (e - i) : ℕ) : ℝ) / (r : ℝ) ^ e)
      Filter.atTop (nhds ((e.centralBinom : ℝ) * (3 / 8 : ℝ) ^ e / e.factorial)) := by
  have h := tendsto_finsetSum (Finset.range (e + 1)) (fun i _ =>
    ((tendsto_const_nhds (x := (e.choose i : ℝ))).mul
      (choose_scaled_limit i _ (3 / 8) mass_scale_atTop mass_scale_limit)).mul
      (choose_scaled_limit (e - i) _ (3 / 8) mass_scale_atTop mass_scale_limit))
  rw [lower_coefficient] at h
  convert h using 1
  funext r
  simp only [Nat.cast_sum, Nat.cast_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ e := by simpa using hi
  have hpow : (r : ℝ) ^ e = (r : ℝ) ^ i * (r : ℝ) ^ (e - i) := by
    rw [← pow_add, Nat.add_sub_of_le hi']
  rw [hpow]
  ring

private theorem block_upper_limit (e : ℕ) :
    Filter.Tendsto (fun r : ℕ => ((e + r).choose e : ℝ) / (r : ℝ) ^ e)
      Filter.atTop (nhds (1 / (e.factorial : ℝ))) := by
  have ha : Filter.Tendsto (fun r : ℕ => e + r) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro n
    filter_upwards [Filter.eventually_ge_atTop n] with r hr
    omega
  have hc : Filter.Tendsto (fun r : ℕ => ((e + r : ℕ) : ℝ) / r)
      Filter.atTop (nhds (1 : ℝ)) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (e : ℝ)).add
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) _ _)
    simp only [zero_add] at h
    apply Filter.Tendsto.congr' _ h
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with r hr
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
    simp [Nat.cast_add, add_div, hr']
  simpa using choose_scaled_limit e _ 1 ha hc

/-- For each fixed e at least three the registered mass bound beats the upper
    endpoint of every sufficiently late original r-block. -/
theorem eventual_signed_count_dominance (e : ℕ) (he : 3 ≤ e) :
    ∃ R : ℕ, ∀ r ≥ R, (e + r).choose e < (signedVectors e (3 * r / 8)).card := by
  have hgap : (1 : ℝ) < (e.centralBinom : ℝ) * (3 / 8 : ℝ) ^ e := by
    have hn := central_coefficient_gap e he
    have hn' : (8 : ℝ) ^ e < (e.centralBinom : ℝ) * (3 : ℝ) ^ e := by exact_mod_cast hn
    rw [div_pow, ← mul_div_assoc]
    exact (lt_div_iff₀ (by positivity : (0 : ℝ) < 8 ^ e)).mpr (by simpa using hn')
  have hfac : (0 : ℝ) < e.factorial := by exact_mod_cast Nat.factorial_pos e
  have hlim := Filter.Tendsto.eventually_lt (block_upper_limit e) (lower_count_limit e)
    ((div_lt_div_iff_of_pos_right hfac).mpr hgap)
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hlim
  refine ⟨R, fun r hr => ?_⟩
  have hstrict := hR r hr
  have hr0 : 0 < r := by
    by_contra hn
    have : r = 0 := by omega
    subst r
    simp [show e ≠ 0 by omega] at hstrict
  have hreal := (div_lt_div_iff_of_pos_right (pow_pos
    (by exact_mod_cast hr0 : (0 : ℝ) < r) e)).mp hstrict
  have hnat : (e + r).choose e <
      ∑ i ∈ Finset.range (e + 1), e.choose i * (3 * r / 8).choose i *
        (3 * r / 8).choose (e - i) := by exact_mod_cast hreal
  exact hnat.trans_le (signed_count_lower_bound e (3 * r / 8))

/-- A collision is converted to disjoint nonnegative exponents on the same generators. -/
theorem bounded_residue_relation (e q m : ℕ) (hm : 0 < m) (g : Fin e → ℕ)
    (hcard : m < (signedVectors e q).card) :
    ∃ a b : Fin e → ℕ, a ≠ b ∧ (∀ i, a i = 0 ∨ b i = 0) ∧
      (∑ i, a i) ≤ 2 * q ∧ (∑ i, b i) ≤ 2 * q ∧
      (∑ i, a i * g i) ≡ (∑ i, b i * g i) [MOD m] := by
  classical
  let : NeZero m := ⟨by omega⟩
  let residue : (Fin e → ℤ) → ZMod m := fun v => ∑ i, (v i : ZMod m) * g i
  have hc : (Finset.univ : Finset (ZMod m)).card < (signedVectors e q).card := by
    simpa [ZMod.card] using hcard
  obtain ⟨v, hv, w, hw, hvw, hres⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc
      (f := residue) (fun _ _ => Finset.mem_univ _)
  have hvb := (mem_signedVectors_iff e q v).mp hv
  have hwb := (mem_signedVectors_iff e q w).mp hw
  let a : Fin e → ℕ := fun i => (v i - w i).toNat
  let b : Fin e → ℕ := fun i => (w i - v i).toNat
  have hdiff (i : Fin e) : (a i : ℤ) - b i = v i - w i := by
    dsimp [a, b]
    omega
  have ha (i : Fin e) : a i ≤ (v i).toNat + (-w i).toNat := by
    dsimp [a]
    omega
  have hb (i : Fin e) : b i ≤ (w i).toNat + (-v i).toNat := by
    dsimp [b]
    omega
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_⟩
  · intro hab
    apply hvw
    funext i
    have := hdiff i
    rw [hab] at this
    omega
  · intro i
    dsimp [a, b]
    omega
  · have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin e))) => ha i)
    rw [Finset.sum_add_distrib] at h
    change (∑ i, a i) ≤ positiveMass v + negativeMass w at h
    omega
  · have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin e))) => hb i)
    rw [Finset.sum_add_distrib] at h
    change (∑ i, b i) ≤ positiveMass w + negativeMass v at h
    omega
  · apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    have hd : (∑ i, (a i : ZMod m) * g i) - (∑ i, (b i : ZMod m) * g i) = 0 := by
      rw [← Finset.sum_sub_distrib]
      calc
        _ = ∑ i, ((v i : ZMod m) - (w i : ZMod m)) * g i := by
          apply Finset.sum_congr rfl
          intro i _
          have hi := congrArg (fun z : ℤ => (z : ZMod m)) (hdiff i)
          push_cast at hi
          rw [← sub_mul, hi]
        _ = residue v - residue w := by
          simp only [residue, sub_mul, Finset.sum_sub_distrib]
        _ = 0 := sub_eq_zero.mpr hres
    simpa only [Nat.cast_sum, Nat.cast_mul] using sub_eq_zero.mp hd

/-- A monomial with the specified exponent vector. -/
def vectorMonomial {e : ℕ} (a : Fin e → ℕ) : MvPolynomial (Fin e) ℚ :=
  MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm a) 1

/-- The polynomial presentation map on the actual multiplicity and generators. -/
def semigroupMap {e : ℕ} (m : ℕ) (g : Fin e → ℕ) :
    MvPolynomial (Option (Fin e)) ℚ →+* MvPolynomial Unit ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun j => MvPolynomial.X () ^ (j.elim m g))

/-- Set the multiplicity variable to zero, retaining every other generator. -/
def reduction (e : ℕ) : MvPolynomial (Option (Fin e)) ℚ →+* MvPolynomial (Fin e) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j => j.elim 0 MvPolynomial.X)

/-- The image of the genuine toric kernel under this reduction. -/
def reducedToricIdeal {e : ℕ} (m : ℕ) (g : Fin e → ℕ) : Ideal (MvPolynomial (Fin e) ℚ) :=
  Ideal.map (reduction e) (RingHom.ker (semigroupMap m g))

/-- The oriented relation before killing the multiplicity variable. -/
def toricRelation {e : ℕ} (a b : Fin e → ℕ) (l : ℕ) :
    MvPolynomial (Option (Fin e)) ℚ :=
  MvPolynomial.rename some (vectorMonomial a) -
    MvPolynomial.X none ^ l * MvPolynomial.rename some (vectorMonomial b)

private theorem monomial_image {e : ℕ} (a g : Fin e → ℕ) :
    (vectorMonomial a).eval₂ MvPolynomial.C (fun i => MvPolynomial.X () ^ g i) =
      (MvPolynomial.X () : MvPolynomial Unit ℚ) ^ (∑ i, a i * g i) := by
  rw [vectorMonomial, MvPolynomial.eval₂_monomial, map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  simp_rw [← pow_mul, Nat.mul_comm (g _) (a _)]
  exact Finset.prod_pow_eq_pow_sum _ _ _

private theorem relation_image {e : ℕ} (m l : ℕ) (g a b : Fin e → ℕ)
    (h : (∑ i, a i * g i) = (∑ i, b i * g i) + m * l) :
    semigroupMap m g (toricRelation a b l) = 0 := by
  simp only [toricRelation, map_sub, map_mul, map_pow, semigroupMap,
    MvPolynomial.eval₂Hom_X', Option.elim_none, MvPolynomial.eval₂Hom_rename]
  change (vectorMonomial a).eval₂ MvPolynomial.C (fun i => MvPolynomial.X () ^ g i) -
    ((MvPolynomial.X () : MvPolynomial Unit ℚ) ^ m) ^ l *
      (vectorMonomial b).eval₂ MvPolynomial.C (fun i => MvPolynomial.X () ^ g i) = 0
  rw [monomial_image, monomial_image, ← pow_mul, ← pow_add, h, Nat.add_comm]
  exact sub_self _

private theorem relation_reduction {e : ℕ} (a b : Fin e → ℕ) (l : ℕ) :
    reduction e (toricRelation a b l) =
      vectorMonomial a - if l = 0 then vectorMonomial b else 0 := by
  change (toricRelation a b l).eval₂ MvPolynomial.C
    (fun j => j.elim 0 MvPolynomial.X) = _
  rw [toricRelation, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_rename, MvPolynomial.eval₂_rename]
  change (vectorMonomial a).eval₂ MvPolynomial.C MvPolynomial.X -
    (0 : MvPolynomial (Fin e) ℚ) ^ l *
      (vectorMonomial b).eval₂ MvPolynomial.C MvPolynomial.X = _
  rw [MvPolynomial.eval₂_eta, MvPolynomial.eval₂_eta]
  by_cases hl : l = 0 <;> simp [hl]

private theorem reduced_relation_nonzero {e : ℕ} (a b : Fin e → ℕ) (l : ℕ)
    (hab : a ≠ b) : reduction e (toricRelation a b l) ≠ 0 := by
  rw [relation_reduction]
  by_cases hl : l = 0
  · simp only [hl, ite_true, sub_ne_zero]
    intro h
    apply hab
    have hs := MvPolynomial.monomial_left_injective (R := ℚ) (by norm_num : (1 : ℚ) ≠ 0) h
    exact congrArg (fun f : Fin e →₀ ℕ => (f : Fin e → ℕ)) hs
  · simp [hl, vectorMonomial]

private theorem reduced_relation_degree {e : ℕ} (a b : Fin e → ℕ) (l d : ℕ)
    (ha : (∑ i, a i) ≤ d) (hb : (∑ i, b i) ≤ d) :
    (reduction e (toricRelation a b l)).totalDegree ≤ d := by
  have hdeg (c : Fin e → ℕ) : (vectorMonomial c).totalDegree = ∑ i, c i := by
    rw [vectorMonomial, MvPolynomial.totalDegree_monomial _ (by norm_num)]
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    rfl
  rw [relation_reduction]
  by_cases hl : l = 0
  · simp only [hl, ite_true]
    exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simpa [hdeg] using ha)
      (by simpa [hdeg] using hb))
  · simpa [hl, hdeg] using ha

/-- Pigeonhole in the actual residue group supplies a nonzero reduced toric relation
    of degree at most twice the signed mass bound. No realization is assumed. -/
theorem exists_bounded_reduced_relation (e q m : ℕ) (hm : 0 < m) (g : Fin e → ℕ)
    (hcard : m < (signedVectors e q).card) :
    ∃ f : MvPolynomial (Fin e) ℚ,
      f ∈ reducedToricIdeal m g ∧ f ≠ 0 ∧ f.totalDegree ≤ 2 * q := by
  obtain ⟨a, b, hab, _, ha, hb, hmod⟩ := bounded_residue_relation e q m hm g hcard
  have horient (a b : Fin e → ℕ) (hab : a ≠ b)
      (ha : (∑ i, a i) ≤ 2 * q) (hb : (∑ i, b i) ≤ 2 * q)
      (hmod : (∑ i, a i * g i) ≡ (∑ i, b i * g i) [MOD m])
      (hle : (∑ i, b i * g i) ≤ (∑ i, a i * g i)) :
      ∃ f : MvPolynomial (Fin e) ℚ,
        f ∈ reducedToricIdeal m g ∧ f ≠ 0 ∧ f.totalDegree ≤ 2 * q := by
    obtain ⟨l, hl⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod.symm
    refine ⟨reduction e (toricRelation a b l), ?_, reduced_relation_nonzero a b l hab,
      reduced_relation_degree a b l (2 * q) ha hb⟩
    apply Ideal.mem_map_of_mem
    exact relation_image m l g a b hl
  rcases le_total (∑ i, b i * g i) (∑ i, a i * g i) with hle | hle
  · exact horient a b hab ha hb hmod hle
  · exact horient b a (Ne.symm hab) hb ha hmod.symm hle

/-- The actual cardinality premise is discharged uniformly throughout the original
    multiplicity block, on the very same generator list used in the kernel. -/
theorem eventual_block_reduced_relation (e : ℕ) (he : 3 ≤ e) :
    ∃ R : ℕ, ∀ r ≥ R, ∀ m : ℕ,
      (e + r - 1).choose (r - 1) ≤ m → m < (e + r).choose r → ∀ g : Fin e → ℕ,
      ∃ f : MvPolynomial (Fin e) ℚ,
        f ∈ reducedToricIdeal m g ∧ f ≠ 0 ∧ f.totalDegree ≤ 2 * (3 * r / 8) := by
  obtain ⟨R, hR⟩ := eventual_signed_count_dominance e he
  refine ⟨max R 1, fun r hr m hlo hhi g => ?_⟩
  have hr1 : 1 ≤ r := (le_max_right R 1).trans hr
  have lower : (e + r - 1).choose (r - 1) = (e + r - 1).choose e := by
    rw [← Nat.choose_symm (by omega : r - 1 ≤ e + r - 1)]
    congr 1
    omega
  have upper : (e + r).choose r = (e + r).choose e := by
    rw [← Nat.choose_symm (by omega : r ≤ e + r), Nat.add_sub_cancel]
  rw [lower] at hlo
  rw [upper] at hhi
  have hm : 0 < m := (Nat.choose_pos (by omega : e ≤ e + r - 1)).trans_le hlo
  exact exists_bounded_reduced_relation e (3 * r / 8) m hm g
    (hhi.trans (hR r ((le_max_left R 1).trans hr)))

end D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation
