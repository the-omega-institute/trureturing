/- GID: D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionSelector
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/CommonPredictionSelector
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: One deterministic majority selector balances every teacher in every mass class. -/

import D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionExteriorCapacity
import Mathlib.Tactic


namespace D5.S3.Arith.FibonacciAtomic.CommonPrediction


section
namespace CapacityCoefficients
noncomputable section
local notation "W" => LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
open scoped BigOperators Polynomial
local notation "P" => Polynomial ℤ
lemma affine_coeff (a b : ℤ) (n j : ℕ) :
    ((Polynomial.C a+Polynomial.C b*Polynomial.X)^n).coeff j =
      (n.choose j:ℤ)*a^(n-j)*b^j := by
  have he : (Polynomial.C a+Polynomial.C b*Polynomial.X)^n =
      ((Polynomial.X+Polynomial.C a)^n).comp (Polynomial.C b*Polynomial.X) := by
    simp only [Polynomial.pow_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
    rw [add_comm]
  rw [he, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_X_add_C_pow]
  ring
lemma V_coeff (n j : ℕ) :
    ((2+(Polynomial.X:P))^n).coeff j=(n.choose j:ℤ)*2^(n-j) := by
  simpa using affine_coeff 2 1 n j
lemma slice_coeff (n k j : ℕ) :
    (WordCounts.slice n k).coeff j=
      (Capacity.pref n j:ℤ)*(Capacity.weight j k:ℤ) := by
  have he : WordCounts.slice n k =
      Polynomial.C ((n.choose k:ℤ)*2^k)*(Polynomial.X^k*(2+Polynomial.X)^(n-k)) := by
    rw [WordCounts.slice_formula]
    simp only [map_mul, map_pow, Polynomial.C_eq_natCast, Polynomial.C_ofNat, mul_pow]
    skip
    ring
  rw [he, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  by_cases hkj : k ≤ j
  · rw [if_pos hkj, V_coeff]
    by_cases hjn : j ≤ n
    · have hexp : n-k-(j-k)=n-j := by omega
      have hch := congrArg (fun x : ℕ => (x:ℤ)) (Nat.choose_mul (n:=n) hkj)
      simp only [Nat.cast_mul] at hch
      rw [hexp]
      unfold Capacity.pref Capacity.weight
      push_cast
      calc
        _ = ((n.choose k:ℤ)*((n-k).choose (j-k):ℤ))*2^(n-j)*2^k := by ring
        _ = _ := by rw [← hch]; ring
    · have hn : n < j := by omega
      have hcj := Nat.choose_eq_zero_of_lt hn
      by_cases hkn : k ≤ n
      · have hck := Nat.choose_eq_zero_of_lt (show n-k < j-k by omega)
        simp [hck, hcj, Capacity.pref]
      · have hck := Nat.choose_eq_zero_of_lt (show n < k by omega)
        simp [hck, hcj, Capacity.pref]
  · have hck := Nat.choose_eq_zero_of_lt (show j < k by omega)
    simp [hkj, hck, Capacity.weight]
lemma low_range (j K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, Capacity.weight j k)=Capacity.low j K := by
  classical
  have hzero (k : ℕ) (hk : k∈Finset.Icc 1 K) (hf : k∉(Finset.Icc 1 K).filter (fun k=>k ≤ j)) :
      Capacity.weight j k=0 := by
    have hkj : j < k := by simpa [hk] using hf
    simp [Capacity.weight, Nat.choose_eq_zero_of_lt hkj]
  have hs := Finset.sum_subset (Finset.filter_subset (fun k=>k ≤ j) (Finset.Icc 1 K)) hzero
  have he : (Finset.Icc 1 K).filter (fun k=>k ≤ j)=
      (Finset.range (j+1)).filter (fun k=>0 < k ∧ k ≤ K) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    omega
  rw [← hs, he, Finset.sum_filter]
  rfl
lemma L_coeff (m j : ℕ) : (ExteriorCounts.L m).coeff j=Capacity.lc m j := by
  have hL : ExteriorCounts.L m=∑ k ∈ Finset.Icc 1 (m/3), WordCounts.slice (m-1) k := by
    unfold ExteriorCounts.L
    simp_rw [WordCounts.slice_formula]
    rfl
  rw [hL, Polynomial.finsetSum_coeff]
  simp_rw [slice_coeff]
  rw [← Finset.mul_sum]
  unfold Capacity.lc
  congr 1
  rw [← Nat.cast_sum, low_range]
end
end CapacityCoefficients

namespace CapacityCoefficients
noncomputable section
local notation "W" => LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
open scoped BigOperators Polynomial
open Capacity
lemma B_coeff (n j : ℕ) :
    ((2+3*(Polynomial.X:P))^n).coeff j = (pref n j:ℤ)*3^j := by
  simpa [pref, Nat.cast_mul, Nat.cast_pow] using affine_coeff 2 3 n j
lemma mulB_coeff (p : P) (j : ℕ) :
    ((2+3*Polynomial.X)*p).coeff j = mulB (fun k => p.coeff k) j := by
  have he : (2+3*Polynomial.X)*p = 2*p+3*(Polynomial.X*p) := by ring
  rw [he, Polynomial.coeff_add]
  cases j with
  | zero => simp [mulB]
  | succ n => simp [mulB]
lemma mulV_coeff (p : P) (j : ℕ) :
    ((2+Polynomial.X)*p).coeff j = mulV (fun k => p.coeff k) j := by
  have he : (2+Polynomial.X)*p = 2*p+Polynomial.X*p := by ring
  rw [he, Polynomial.coeff_add]
  cases j with
  | zero => simp [mulV]
  | succ n => simp [mulV]
lemma shift_coeff (p : P) (z : ℕ) :
    (2*Polynomial.X^2*p).coeff z = if 2 ≤ z then 2*p.coeff (z-2) else 0 := by
  have he : 2*Polynomial.X^2*p = 2*(Polynomial.X^2*p) := by ring
  rw [he, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X_pow_mul']
  split_ifs <;> simp
lemma E_coeff (m z : ℕ) :
    (ExteriorCounts.Eformula m).coeff z = 2*discrepancy_half m z := by
  unfold ExteriorCounts.Eformula
  rw [mul_assoc (2*Polynomial.X^2) (2+Polynomial.X), shift_coeff]
  unfold discrepancy_half
  split_ifs
  · rw [mulV_coeff, mulV]
    have hD (j : ℕ) :
        (((2+3*Polynomial.X)*ExteriorCounts.L m-
          4*((2+3*Polynomial.X)^(m-1)-(2+Polynomial.X)^(m-1))):P).coeff j=dc m j := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_ofNat_mul, Polynomial.coeff_sub,
        mulB_coeff]
      simp_rw [L_coeff, B_coeff, V_coeff]
      rfl
    simp_rw [hD]
    rfl
  · simp
lemma N_coeff (m z : ℕ) (hmpos : 0 < m) :
    (ReservoirWords.Nz m z:ℤ)=2*reservoir_half m z := by
  have he : (ReservoirWords.Nz m z:ℤ) =
      (2*Polynomial.X^2*(2+Polynomial.X)*(2+3*Polynomial.X)^m:P).coeff z := by
    rw [ReservoirWords.actual_Nz_identity]
    have hm := Polynomial.coeff_map (f := Nat.castRingHom ℤ)
      (p := (2*(Polynomial.X : Polynomial ℕ)^2*(2+(Polynomial.X : Polynomial ℕ))*(2+3*(Polynomial.X : Polynomial ℕ))^m)) (n := z)
    simpa only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_natCast, Polynomial.map_ofNat, Polynomial.map_X, Nat.coe_castRingHom, Nat.cast_ofNat] using hm.symm
  rw [he]
  have hp : (2*Polynomial.X^2*(2+Polynomial.X)*(2+3*Polynomial.X)^m:P)=
      2*Polynomial.X^2*((2+Polynomial.X)*((2+3*Polynomial.X)*(2+3*Polynomial.X)^(m-1))) := by
    have hpow : (2+3*(Polynomial.X:P))^m=(2+3*Polynomial.X)*(2+3*Polynomial.X)^(m-1) := by
      conv_lhs => rw [show m=(m-1)+1 by omega, pow_succ]
      ring
    rw [hpow]
    ring
  rw [hp, shift_coeff]
  unfold reservoir_half
  split_ifs
  · rw [mulV_coeff, mulV]
    have hN (j : ℕ) : (((2+3*Polynomial.X)*(2+3*Polynomial.X)^(m-1)):P).coeff j=nc m j := by
      rw [mulB_coeff]
      simp_rw [B_coeff]
      rfl
    simp_rw [hN]
    rfl
  · simp
end
end CapacityCoefficients
end

section
open D5.S3.Arith.FibonacciAtomic
open LiteralWindowEnd (first last)
open LegalPriorityTeacher (Input teacher)
open scoped BigOperators Polynomial
attribute [local instance] Classical.propDecidable
namespace CommonSelector
noncomputable section
open ExteriorCounts
open WordCounts (rareN)
def label {m : ℕ} (side : Bool) (i : Fin m) (x : Input (m+3)) : Fin 3 :=
  if side then teacher (TeacherLabels.rightRoles i) x else teacher (TeacherLabels.leftRoles i) x
def outsideCount {m : ℕ} (z : ℕ) (side : Bool) (i : Fin m) : ℤ :=
  ∑ x : Input (m+3), if ¬ReservoirWords.isReservoir x ∧ rareN x=z then
    MajorityGeometry.err (label side i x) (exteriorSelector x) else 0
def prefEquiv {m : ℕ} (σ : Equiv.Perm (Fin m)) : (Fin m → W) ≃ (Fin m → W) where
  toFun p := p ∘ σ
  invFun p := p ∘ σ.symm
  left_inv p := by funext i; simp
  right_inv p := by funext i; simp
def wordPerm {m : ℕ} (σ : Equiv.Perm (Fin m)) : Input (m+3) ≃ Input (m+3) :=
  (Fin.appendEquiv m 3).symm.trans
    ((Equiv.prodCongr (prefEquiv σ) (Equiv.refl (Fin 3 → W))).trans (Fin.appendEquiv m 3))
lemma wordPerm_append {m : ℕ} (σ : Equiv.Perm (Fin m)) (p : Fin m → W) (a : Fin 3 → W) :
    wordPerm σ (Fin.append p a)=Fin.append (p ∘ σ) a := by
  change (Fin.appendEquiv m 3) ((Equiv.prodCongr (prefEquiv σ) (Equiv.refl _))
    ((Fin.appendEquiv m 3).symm ((Fin.appendEquiv m 3) (p,a)))) = _
  rw [Equiv.symm_apply_apply]
  rfl
lemma wordPerm_views {m : ℕ} (σ : Equiv.Perm (Fin m)) (x : Input (m+3)) :
    wordPerm σ x=Fin.append ((pref x) ∘ σ) ![q x,r x,v x] := by
  conv_lhs => rw [←append_views x, wordPerm_append]
lemma rare_perm {m : ℕ} (σ : Equiv.Perm (Fin m)) (x : Input (m+3)) :
    rareN (wordPerm σ x)=rareN x := by
  rw [wordPerm_views]
  exact (ReservoirWords.actual_prefix_perm (pref x) ![q x,r x,v x] σ).1.trans
    (congrArg rareN (append_views x))
lemma res_perm {m : ℕ} (σ : Equiv.Perm (Fin m)) (x : Input (m+3)) :
    ReservoirWords.isReservoir (wordPerm σ x) ↔ ReservoirWords.isReservoir x := by
  rw [wordPerm_views]
  simpa only [append_views] using (ReservoirWords.actual_prefix_perm (pref x) ![q x,r x,v x] σ).2
lemma selector_perm {m : ℕ} (σ : Equiv.Perm (Fin m)) (x : Input (m+3)) :
    exteriorSelector (wordPerm σ x)=exteriorSelector x := by
  rw [wordPerm_views]
  simpa only [append_views] using exterior_prefix_permutation (pref x) (q x) (r x) (v x) σ
lemma label_swap {m : ℕ} (i j : Fin m) (side : Bool) (x : Input (m+3)) :
    label side i (wordPerm (Equiv.swap i j) x)=label side j x := by
  have ha := TeacherLabels.actual_left_label (pref x) ![q x,r x,v x] j
  have hb := TeacherLabels.actual_right_label (pref x) ![q x,r x,v x] j
  rw [append_views] at ha hb
  rw [wordPerm_views]
  cases side
  · simpa only [label, Bool.false_eq_true, ↓reduceIte, TeacherLabels.actual_left_label,
      Function.comp_apply, Equiv.swap_apply_left] using ha.symm
  · simpa only [label, Bool.true_eq, ↓reduceIte, TeacherLabels.actual_right_label,
      Function.comp_apply, Equiv.swap_apply_left] using hb.symm
lemma outsideCount_equal {m : ℕ} (z : ℕ) (side : Bool) (i j : Fin m) :
    outsideCount z side i=outsideCount z side j := by
  let F : Input (m+3) → ℤ := fun x => if ¬ReservoirWords.isReservoir x ∧ rareN x=z then
    MajorityGeometry.err (label side i x) (exteriorSelector x) else 0
  calc
    outsideCount z side i = ∑ x, F (wordPerm (Equiv.swap i j) x) :=
      (Equiv.sum_comp (wordPerm (Equiv.swap i j)) F).symm
    _ = outsideCount z side j := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [F, rare_perm, res_perm, selector_perm, label_swap]
end
end CommonSelector
end

section
open D5.S3.Arith.FibonacciAtomic
open LegalPriorityTeacher (Input teacher)
open scoped BigOperators Polynomial
attribute [local instance] Classical.propDecidable
namespace CommonSelector
noncomputable section
open ExteriorCounts
open WordCounts (rareN)
lemma actual_flat {m : ℕ} (x : Input (m+3)) (hx : ReservoirWords.isReservoir x) (i : Fin m) :
    teacher (TeacherLabels.leftRoles i) x=0 ∧ teacher (TeacherLabels.rightRoles i) x=2 := by
  have hres : ReservoirWords.qok (q x) ∧ r x=.high ∧ ReservoirWords.vok (v x) := hx
  have hq : q x=.zero ∨ q x=.middle ∨ q x=.high := by
    simpa [ReservoirWords.qok] using hres.1
  have hv : v x=.low ∨ v x=.ends := by simpa [ReservoirWords.vok] using hres.2.2
  have hword : Fin.append (pref x) ![q x,.high,v x]=x := by
    rw [←hres.2.1]
    exact append_views x
  rw [←hword]
  exact TeacherLabels.actual_reservoir_flat (pref x) (q x) (v x) hq hv i
lemma reservoir_majority {m : ℕ} (x : Input (m+3)) (hx : ReservoirWords.isReservoir x)
    (c d : Fin 3) (hd : d=0 ∨ d=2) : actualVotes x c ≤ actualVotes x d := by
  have hleft : ∀ i, teacher (TeacherLabels.leftRoles i) x=0 := fun i => (actual_flat x hx i).1
  have hright : ∀ i, teacher (TeacherLabels.rightRoles i) x=2 := fun i => (actual_flat x hx i).2
  simp only [actualVotes]
  simp_rw [hleft, hright]
  rcases hd with rfl | rfl <;> fin_cases c <;> simp

def Rset (m z : ℕ) : Finset (Input (m+3)) :=
  Finset.univ.filter (fun x => ReservoirWords.isReservoir x ∧ rareN x=z)
def reservoirClassEquiv (m z : ℕ) :
    {x : {x : LegalPriorityTeacher.Input (m+3) // ReservoirWords.isReservoir x} // ReservoirWords.rs x.val=z} ≃
      {x : Input (m+3) // ReservoirWords.isReservoir x ∧ rareN x=z} where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv x := rfl
  right_inv x := rfl
lemma Rset_card (m z : ℕ) : (Rset m z).card=ReservoirWords.Nz m z := by
  have hc := Fintype.card_congr (reservoirClassEquiv m z)
  change ReservoirWords.Nz m z = _ at hc
  rw [Fintype.card_subtype] at hc
  exact hc.symm
lemma exists_split (m z : ℕ) (hm : 0 < m) :
    ∃ S : Finset (Input (m+3)), S ⊆ Rset m z ∧
      (Eformula m).coeff z+2*(S.card:ℤ)-(ReservoirWords.Nz m z:ℤ)=0 := by
  obtain ⟨t,ht,hbal⟩ := Capacity.integer_split_positive m z hm
  have hN := CapacityCoefficients.N_coeff m z hm
  have hE := CapacityCoefficients.E_coeff m z
  have hc : t ≤ (Rset m z).card := by
    rw [Rset_card]
    have hh : (t:ℤ) ≤ (ReservoirWords.Nz m z:ℤ) := by omega
    exact_mod_cast hh
  obtain ⟨S,hS,hcard⟩ := Finset.exists_subset_card_eq hc
  refine ⟨S,hS,?_⟩
  rw [hcard]
  omega

def classifier {m : ℕ} (S : ℕ → Finset (Input (m+3))) (x : Input (m+3)) : Fin 3 :=
  if ReservoirWords.isReservoir x then if x ∈ S (rareN x) then 2 else 0 else exteriorSelector x
lemma classifier_majority {m : ℕ} (S : ℕ → Finset (Input (m+3)))
    (x : Input (m+3)) (c : Fin 3) : actualVotes x c ≤ actualVotes x (classifier S x) := by
  by_cases hr : ReservoirWords.isReservoir x
  · apply reservoir_majority x hr c
    by_cases hs : x ∈ S (rareN x) <;> simp [classifier, hr, hs]
  · simpa only [classifier, if_neg hr] using exterior_majority x c

def errorCount {m : ℕ} (z : ℕ) (side : Bool) (i : Fin m)
    (f : Input (m+3) → Fin 3) : ℤ :=
  ∑ x : Input (m+3), if rareN x=z then MajorityGeometry.err (label side i x) (f x) else 0
lemma indicator_sum {m : ℕ} (S : Finset (Input (m+3))) :
    (∑ x : Input (m+3), if x∈S then (1:ℤ) else 0)=(S.card:ℤ) := by
  rw [←Finset.sum_filter]
  simp
lemma leftCount {m : ℕ} (S : ℕ → Finset (Input (m+3)))
    (hS : ∀ z, S z ⊆ Rset m z) (z : ℕ) (i : Fin m) :
    errorCount z false i (classifier S)=outsideCount z false i+(S z).card := by
  have hpoint (x : Input (m+3)) :
      (if rareN x=z then MajorityGeometry.err (label false i x) (classifier S x) else 0)=
      (if ¬ReservoirWords.isReservoir x ∧ rareN x=z then
        MajorityGeometry.err (label false i x) (exteriorSelector x) else 0)+
      (if x∈S z then (1:ℤ) else 0) := by
    have hin : x∈S z → ReservoirWords.isReservoir x ∧ rareN x=z := by
      intro hx
      exact (Finset.mem_filter.mp (hS z hx)).2
    by_cases hz : rareN x=z
    · by_cases hr : ReservoirWords.isReservoir x
      · have hf := (actual_flat x hr i).1
        by_cases hs : x∈S z <;> simp [label, classifier, hz, hr, hs, hf, MajorityGeometry.err]
      · have hs : x∉S z := fun hx => hr (hin hx).1
        simp [label, classifier, hz, hr, hs]
    · have hs : x∉S z := fun hx => hz (hin hx).2
      simp [hz, hs]
  unfold errorCount outsideCount
  rw [Finset.sum_congr rfl (fun x _ => hpoint x), Finset.sum_add_distrib, indicator_sum]
lemma rightCount {m : ℕ} (S : ℕ → Finset (Input (m+3)))
    (hS : ∀ z, S z ⊆ Rset m z) (z : ℕ) (i : Fin m) :
    errorCount z true i (classifier S)=outsideCount z true i+
      (ReservoirWords.Nz m z:ℤ)-(S z).card := by
  have hpoint (x : Input (m+3)) :
      (if rareN x=z then MajorityGeometry.err (label true i x) (classifier S x) else 0)=
      (if ¬ReservoirWords.isReservoir x ∧ rareN x=z then
        MajorityGeometry.err (label true i x) (exteriorSelector x) else 0)+
      (if x∈Rset m z then (1:ℤ) else 0)-(if x∈S z then (1:ℤ) else 0) := by
    have hin : x∈S z → ReservoirWords.isReservoir x ∧ rareN x=z := by
      intro hx
      exact (Finset.mem_filter.mp (hS z hx)).2
    by_cases hz : rareN x=z
    · by_cases hr : ReservoirWords.isReservoir x
      · have hf := (actual_flat x hr i).2
        by_cases hs : x∈S z <;> simp [label, classifier, hz, hr, hs, hf, Rset, MajorityGeometry.err]
      · have hs : x∉S z := fun hx => hr (hin hx).1
        simp [label, classifier, hz, hr, hs, Rset]
    · have hs : x∉S z := fun hx => hz (hin hx).2
      simp [hz, hs, Rset]
  unfold errorCount outsideCount
  rw [Finset.sum_congr rfl (fun x _ => hpoint x), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, indicator_sum, indicator_sum, Rset_card]
end
end CommonSelector
end

section
open D5.S3.Arith.FibonacciAtomic
open LegalPriorityTeacher (Input)
open scoped BigOperators
namespace CommonSelector
noncomputable section
open ExteriorCounts
open WordCounts (rareN)
lemma outsideDifference {m : ℕ} (z : ℕ) (i : Fin m) :
    outsideCount z false i-outsideCount z true i=Ez m z i := by
  unfold outsideCount Ez
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : ¬ReservoirWords.isReservoir x ∧ rareN x=z <;> simp [h, label]

def UniformMassBalanced : Prop :=
  ∀ m : ℕ, 0 < m → ∃ f : Input (m+3) → Fin 3,
    (∀ x c, actualVotes x c ≤ actualVotes x (f x)) ∧
    (∀ z, ∀ i j : Fin m,
      errorCount z false i f=errorCount z false j f ∧
      errorCount z false i f=errorCount z true j f)

theorem uniform_mass_balanced : UniformMassBalanced := by
  intro m hm
  choose S hS hbal using fun z => exists_split m z hm
  refine ⟨classifier S, classifier_majority S, ?_⟩
  have hcross (z : ℕ) (i : Fin m) :
      errorCount z false i (classifier S)=errorCount z true i (classifier S) := by
    rw [leftCount S hS, rightCount S hS]
    have he := actual_Ez_identity m z hm i
    have hd := outsideDifference z i
    have hb := hbal z
    omega
  intro z i j
  have hleft : errorCount z false i (classifier S)=errorCount z false j (classifier S) := by
    rw [leftCount S hS, leftCount S hS, outsideCount_equal z false i j]
  exact ⟨hleft, hleft.trans (hcross z j)⟩
end
end CommonSelector
end

end D5.S3.Arith.FibonacciAtomic.CommonPrediction
