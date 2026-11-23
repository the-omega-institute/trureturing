/- GID: D5/S3/Quantum/Entanglement/SectorChannels/MaxentRankPhaseRounding
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/SectorChannels/MaxentRankPhaseRounding
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact nearest rank counts and sharp fixed-phase scalar cap packing. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace D5.S3.Quantum.Entanglement.SectorChannels.MaxentRankPhaseRounding

set_option autoImplicit false
open scoped BigOperators

/-! # Nearest integer phase versus maximally entangled scalar packing
Integer-count minimization, sharp finite budget comparison and near-phase continuity.
The greedy packing is a scalar definition; physical channel attainment is not asserted.
-/
namespace RTMaxentRounding

section HeadTail
/-- The mass discrepancy between the unit-rounded head and the squared caps. -/
noncomputable def deficit (K : ℕ) (c : Fin K → ℝ) : ℝ :=
  ∑ i, (1-(c i)^2)

/-- The variable part of the packed error: the same deficit minus the tail hit mass. -/
noncomputable def packedLoss {A : Type*} [Fintype A] (K : ℕ) (c : Fin K → ℝ) (y : A → ℝ) : ℝ :=
  deficit K c - ∑ a, (y a)^2

/-- The sharp finite-head estimate. The first K capacities are already
full; the sum of all inserted tail amplitudes is their missing unit mass.
Neither the tail ordering nor an assumption about its cardinal is needed. -/
private theorem sharp_head_tail {A : Type*} [Fintype A] (K : ℕ) (c : Fin K → ℝ) (y : A → ℝ)
    (u : ℝ) (hu : 0≤u) (_hu1 : u≤1)
    (hc : ∀ i, u≤c i ∧ c i≤1)
    (hy : ∀ a, 0≤y a ∧ y a≤u)
    (budget : (∑ a, y a) = ∑ i, (1-c i)) :
    0≤deficit K c ∧
    ((K:ℝ)+1)/(2*(K:ℝ)+1)*deficit K c ≤ packedLoss K c y ∧
    packedLoss K c y ≤ deficit K c ∧
    deficit K c - (deficit K c)^2 ≤ packedLoss K c y := by
  classical
  let T : ℝ := ∑ a, y a
  let S : ℝ := ∑ a, (y a)^2
  let D := deficit K c
  let k : ℝ := K
  have hk : 0≤k := Nat.cast_nonneg K
  have hT : 0≤T := Finset.sum_nonneg (fun a _ => (hy a).1)
  have hS : 0≤S := Finset.sum_nonneg (fun a _ => sq_nonneg (y a))
  have hDT : (1+u)*T ≤ D := by
    calc
      (1+u)*T = ∑ i, (1+u)*(1-c i) := by
        change (1+u)*(∑ a, y a) = _
        rw [budget,Finset.mul_sum]
      _ ≤ D := by
        apply Finset.sum_le_sum
        intro i _
        have hh := mul_nonneg (sub_nonneg.mpr (hc i).1) (sub_nonneg.mpr (hc i).2)
        nlinarith
  have hTcap : T ≤ k*(1-u) := by
    calc
      T = ∑ i, (1-c i) := budget
      _ ≤ ∑ _i : Fin K, (1-u) :=
        Finset.sum_le_sum (fun i _ => sub_le_sub_left (hc i).1 1)
      _ = k*(1-u) := by simp [k,nsmul_eq_mul]; ring
  have hSu : S ≤ u*T := by
    change (∑ a, (y a)^2) ≤ u*(∑ a, y a)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => by
      nlinarith [mul_nonneg (hy a).1 (sub_nonneg.mpr (hy a).2)]
  have hST : S ≤ T^2 := by
    change (∑ a, (y a)^2) ≤ T^2
    calc
      _ ≤ ∑ a, T*y a := by
        apply Finset.sum_le_sum
        intro a _
        have hya : y a≤T := Finset.single_le_sum (fun i _ => (hy i).1) (Finset.mem_univ a)
        nlinarith [mul_nonneg (hy a).1 (sub_nonneg.mpr hya)]
      _ = T^2 := by rw [← Finset.mul_sum]; change T*T=T^2; ring
  have hTD : T ≤ D := by
    calc
      T = 1*T := (one_mul T).symm
      _ ≤ (1+u)*T := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hu) hT
      _ ≤ D := hDT
  have hD : 0≤D := le_trans hT hTD
  have hST' : S ≤ T*T := by simpa [pow_two] using hST
  have hfactor : 0≤2*k+1 := by linarith
  have hm : (2*k+1)*S ≤ k*D := by
    by_cases h : u*(k+1)≤k
    · calc
        (2*k+1)*S ≤ (2*k+1)*(u*T) := mul_le_mul_of_nonneg_left hSu hfactor
        _ = ((2*k+1)*u)*T := by ring
        _ ≤ (k*(1+u))*T := mul_le_mul_of_nonneg_right (by nlinarith) hT
        _ = k*((1+u)*T) := by ring
        _ ≤ k*D := mul_le_mul_of_nonneg_left hDT hk
    · have hh : (2*k+1)*T ≤ k*(1+u) := by
        have h₀ : (2*k+1)*(1-u)≤1+u := by nlinarith
        calc
          (2*k+1)*T ≤ (2*k+1)*(k*(1-u)) := mul_le_mul_of_nonneg_left hTcap hfactor
          _ = k*((2*k+1)*(1-u)) := by ring
          _ ≤ k*(1+u) := mul_le_mul_of_nonneg_left h₀ hk
      calc
        (2*k+1)*S ≤ (2*k+1)*(T*T) := mul_le_mul_of_nonneg_left hST' hfactor
        _ = ((2*k+1)*T)*T := by ring
        _ ≤ (k*(1+u))*T := mul_le_mul_of_nonneg_right hh hT
        _ = k*((1+u)*T) := by ring
        _ ≤ k*D := mul_le_mul_of_nonneg_left hDT hk
  change 0≤D ∧ (k+1)/(2*k+1)*D≤D-S ∧ D-S≤D ∧ D-D^2≤D-S
  refine ⟨hD,?_,sub_le_self _ hS,?_⟩
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0<2*k+1 by linarith)).2
    nlinarith
  · nlinarith [mul_nonneg (sub_nonneg.mpr hTD) (add_nonneg hD hT)]

/-- Scale the same finite-head estimate to the error and distance of the
max-ent diagonal packing model. The factor approaches one half only as
the number of rounded-up coordinates grows. -/
private theorem sharp_scaled {A : Type*} [Fintype A] (K : ℕ) (c : Fin K → ℝ) (y : A → ℝ)
    (u r : ℝ) (hr : 0<r) (hu : 0≤u) (hu1 : u≤1)
    (hc : ∀ i, u≤c i ∧ c i≤1) (hy : ∀ a, 0≤y a ∧ y a≤u)
    (budget : (∑ a, y a) = ∑ i, (1-c i)) :
    let Δ := 2*deficit K c/r
    let E := 2*packedLoss K c y/r
    ((K:ℝ)+1)/(2*(K:ℝ)+1)*Δ ≤ E ∧ E≤Δ ∧ Δ*(1-r*Δ/2)≤E := by
  dsimp only
  obtain ⟨hD,hlo,hhi,hnear⟩ := sharp_head_tail K c y u hu hu1 hc hy budget
  have hr' : 0≤(2:ℝ)/r := div_nonneg (by norm_num) hr.le
  refine ⟨?_,?_,?_⟩
  · calc
      _ = (2/r)*((((K:ℝ)+1)/(2*(K:ℝ)+1))*deficit K c) := by ring
      _ ≤ (2/r)*packedLoss K c y := mul_le_mul_of_nonneg_left hlo hr'
      _ = _ := by ring
  · exact (div_le_div_iff_of_pos_right hr).2 (by linarith)
  · have he : r*(2*deficit K c/r)/2=deficit K c := by
      rw [div_eq_mul_inv]
      have hinv : r*r⁻¹=1 := mul_inv_cancel₀ hr.ne'
      calc
        r*(2*deficit K c*r⁻¹)/2=(r*r⁻¹)*deficit K c := by ring
        _ = _ := by rw [hinv,one_mul]
    rw [he]
    calc
      _ = (2/r)*(deficit K c-(deficit K c)^2) := by ring
      _ ≤ (2/r)*packedLoss K c y := mul_le_mul_of_nonneg_left hnear hr'
      _ = _ := by ring

end HeadTail

section IntegerPhase
def roundedOffset (chosen : Bool) : ℤ := if chosen then 1 else 0

private theorem supporting_slope (f c : ℝ) (hf0 : 0≤f) (hf1 : f≤1) (hc : 0≤c) (hc1 : c≤1)
    (chosen : Bool) (hy : if chosen then c≤f else f≤c) (d : ℤ) :
    |(d:ℝ)-f| - |((roundedOffset chosen : ℤ):ℝ)-f| ≥
      (1-2*c)*((d:ℝ)-(roundedOffset chosen:ℤ)) := by
  have hcases : d≤0 ∨ 1≤d := by omega
  cases chosen
  · have hcf : f≤c := hy
    rw [show (roundedOffset false : ℝ)=0 by norm_num [roundedOffset]]
    change |(d:ℝ)-f|-|0-f| ≥ (1-2*c)*((d:ℝ)-0)
    rw [abs_of_nonpos (by linarith : 0-f≤0)]
    rcases hcases with h|h
    · have hd : (d:ℝ)≤0 := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith : (d:ℝ)-f≤0)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (neg_nonneg.mpr hd)]
    · have hd : 1≤(d:ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith : 0≤(d:ℝ)-f)]
      nlinarith [mul_nonneg hc (show 0≤(d:ℝ)-1 by linarith)]
  · have hcf : c≤f := hy
    rw [show (roundedOffset true : ℝ)=1 by norm_num [roundedOffset]]
    change |(d:ℝ)-f|-|1-f| ≥ (1-2*c)*((d:ℝ)-1)
    rw [abs_of_nonneg (by linarith : 0≤1-f)]
    rcases hcases with h|h
    · have hd : (d:ℝ)≤0 := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith : (d:ℝ)-f≤0)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (neg_nonneg.mpr hd)]
    · have hd : 1≤(d:ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith : 0≤(d:ℝ)-f)]
      nlinarith [mul_nonneg hc (show 0≤(d:ℝ)-1 by linarith)]

/-- Largest-remainder rounding is optimal among all integer offsets,
including arbitrary negative offsets. A threshold passes through the
chosen largest remainders, with arbitrary tie choices. -/
private theorem integer_offset_minimum {A : Type*} [Fintype A]
    (f : A → ℝ) (chosen : A → Bool) (d : A → ℤ) (c : ℝ)
    (hc : 0≤c) (hc1 : c≤1)
    (hf : ∀ i, 0≤f i ∧ f i≤1)
    (ht : ∀ i, if chosen i then c≤f i else f i≤c)
    (hs : (∑ i, d i) = ∑ i, roundedOffset (chosen i)) :
    (∑ i, |(roundedOffset (chosen i):ℝ)-f i|) ≤
      ∑ i, |(d i:ℝ)-f i| := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    supporting_slope (f i) c (hf i).1 (hf i).2 hc hc1 (chosen i) (ht i) (d i))
  have hsR : (∑ i, (d i:ℝ)) = ∑ i, (roundedOffset (chosen i):ℝ) := by exact_mod_cast hs
  rw [← Finset.mul_sum,Finset.sum_sub_distrib,hsR,sub_self,mul_zero,Finset.sum_sub_distrib] at h
  linarith

/-- If fractional masses add to the count of marked labels, the exact
unscaled optimum is twice the deficit of the marked labels. -/
private theorem rounded_error_eq_twice_deficit {A : Type*} [Fintype A]
    (f : A → ℝ) (chosen : A → Bool) (hf : ∀ i, 0≤f i ∧ f i≤1)
    (hs : (∑ i, f i) = ∑ i, (roundedOffset (chosen i):ℝ)) :
    (∑ i, |(roundedOffset (chosen i):ℝ)-f i|) =
      2*∑ i, if chosen i then 1-f i else 0 := by
  have h (i : A) : |(roundedOffset (chosen i):ℝ)-f i| =
      2*(if chosen i then 1-f i else 0)+(f i-(roundedOffset (chosen i):ℝ)) := by
    cases hi : chosen i
    · rw [show (roundedOffset false : ℝ)=0 by norm_num [roundedOffset]]
      change |0-f i|=2*0+(f i-0)
      rw [abs_of_nonpos (by linarith [(hf i).1] : 0-f i≤0)]
      linarith
    · rw [show (roundedOffset true : ℝ)=1 by norm_num [roundedOffset]]
      change |1-f i|=2*(1-f i)+(f i-1)
      rw [abs_of_nonneg (by linarith [(hf i).2] : 0≤1-f i)]
      linarith
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hs,
    sub_self, add_zero]

end IntegerPhase

section GreedyBridge
def sums (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, f i

/-- The readout of the ordinary left-to-right scalar greedy allocation. -/
def greedyAt (c : ℕ → ℝ) (B : ℝ) (i : ℕ) : ℝ :=
  min (c i) (max 0 (B - sums c i))

private theorem sums_succ (f : ℕ → ℝ) (n : ℕ) : sums f (n+1)=sums f n+f n :=
  Finset.sum_range_succ f n

private theorem sums_split (f : ℕ → ℝ) (m n : ℕ) :
    sums f (m+n)=sums f m + ∑ i : Fin n, f (m+i.val) := by
  unfold sums
  rw [Finset.sum_range_add]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => f (m+i)) n).symm

private theorem sums_fin (f : ℕ → ℝ) (n : ℕ) :
    sums f n = ∑ i : Fin n, f i.val :=
  (Fin.sum_univ_eq_sum_range f n).symm

private theorem greedy_mass (c : ℕ → ℝ) (B : ℝ) (n : ℕ)
    (hB : 0≤B) (hc : ∀ i<n, 0≤c i) :
    sums (greedyAt c B) n = min B (sums c n) := by
  induction n with
  | zero => simp [sums, min_eq_right hB]
  | succ n ih =>
    have hcₙ := hc n (Nat.lt_succ_self n)
    rw [sums_succ, sums_succ, ih (fun i hi => hc i (Nat.lt_trans hi (Nat.lt_succ_self n)))]
    unfold greedyAt
    by_cases hb : B≤sums c n
    · rw [min_eq_left hb, max_eq_left (sub_nonpos.mpr hb),min_eq_right hcₙ,
        min_eq_left (by linarith : B≤sums c n+c n),add_zero]
    · have hb' : sums c n≤B := le_of_lt (lt_of_not_ge hb)
      rw [min_eq_right hb', max_eq_right (sub_nonneg.mpr hb')]
      by_cases h : sums c n+c n≤B
      · rw [min_eq_left (by linarith : c n≤B-sums c n),min_eq_right h]
      · rw [min_eq_right (by linarith : B-sums c n≤c n),
          min_eq_left (by linarith : B≤sums c n+c n)]
        linarith

private theorem greedy_head (K : ℕ) (c : ℕ → ℝ) (hc : ∀ i<K, c i≤1)
    (i : ℕ) (hi : i<K) : greedyAt c K i=c i := by
  have h : sums c (i+1) ≤ (i:ℝ)+1 := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (i+1), (1:ℝ) :=
        Finset.sum_le_sum fun j hj => hc j (lt_of_lt_of_le (Finset.mem_range.mp hj) hi)
      _ = _ := by simp
  rw [sums_succ] at h
  have hK : (i:ℝ)+1≤(K:ℝ) := by exact_mod_cast hi
  apply min_eq_left
  exact le_trans (show c i≤(K:ℝ)-sums c i by linarith) (le_max_right _ _)

/-- The sharp comparison for the literal greedy scalar readout. Input
capacities are square roots of the fractional parts, so their squares
sum to the integer residual budget K. The head/tail hypotheses may be
obtained by sorting; this lemma itself requires no sorting algorithm. -/
private theorem greedy_phase_bound (K N : ℕ) (r u : ℝ) (c : ℕ → ℝ)
    (hr : 0<r) (hu : 0≤u) (hu1 : u≤1)
    (hc : ∀ i<K+N, 0≤c i ∧ c i≤1)
    (hhead : ∀ i<K, u≤c i) (htail : ∀ i : Fin N, c (K+i.val)≤u)
    (hfrac : sums (fun i => (c i)^2) (K+N) = (K:ℝ)) :
    let Δ := 2*((K:ℝ)-sums (fun i => (c i)^2) K)/r
    let E := 2*((K:ℝ)-sums (fun i => (greedyAt c K i)^2) (K+N))/r
    ((K:ℝ)+1)/(2*(K:ℝ)+1)*Δ ≤ E ∧ E≤Δ ∧ Δ*(1-r*Δ/2)≤E := by
  let x : Fin K → ℝ := fun i => c i.val
  let y : Fin N → ℝ := fun i => greedyAt c K (K+i.val)
  have hK : 0≤(K:ℝ) := Nat.cast_nonneg K
  have hh : ∀ i<K, greedyAt c K i=c i :=
    fun i hi => greedy_head K c (fun j hj => (hc j (lt_of_lt_of_le hj (Nat.le_add_right K N))).2) i hi
  have hsum : (K:ℝ)≤sums c (K+N) := by
    rw [← hfrac]
    exact Finset.sum_le_sum (fun i hi => by
      obtain ⟨h0,h1⟩ := hc i (Finset.mem_range.mp hi)
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)])
  have hg := greedy_mass c K (K+N) hK (fun i hi => (hc i hi).1)
  rw [min_eq_left hsum, sums_split, sums_fin (greedyAt c K) K] at hg
  have hfin : (∑ i : Fin K, greedyAt c K i.val) = ∑ i : Fin K, x i := by
    exact Finset.sum_congr rfl (fun i _ => hh i.val i.isLt)
  rw [hfin] at hg
  have hb : (∑ i, y i) = ∑ i, (1-x i) := by
    rw [Finset.sum_sub_distrib]
    simp
    change (∑ i : Fin N, greedyAt c K (K+i.val)) = _
    linarith
  have hxy := sharp_scaled K x y u r hr hu hu1
    (fun i => ⟨hhead i.val i.isLt,(hc i.val (lt_of_lt_of_le i.isLt (Nat.le_add_right K N))).2⟩)
    (fun i => ⟨le_min ((hc _ (Nat.add_lt_add_left i.isLt K)).1) (le_max_left _ _),
      (min_le_left _ _).trans (htail i)⟩) hb
  have hdef : deficit K x = (K:ℝ)-sums (fun i => (c i)^2) K := by
    unfold deficit
    rw [Finset.sum_sub_distrib,sums_fin]
    simp [x]
  have hpack : packedLoss K x y =
      (K:ℝ)-sums (fun i => (greedyAt c K i)^2) (K+N) := by
    unfold packedLoss
    rw [hdef,sums_split,sums_fin (fun i => (greedyAt c K i)^2) K, sums_fin (fun i => (c i)^2) K]
    have hsq : (∑ i : Fin K, (greedyAt c K i.val)^2) = ∑ i : Fin K, (c i.val)^2 :=
      Finset.sum_congr rfl (fun i _ => congrArg (·^2) (hh i.val i.isLt))
    rw [hsq]
    change _ - (∑ i : Fin N, (greedyAt c K (K+i.val))^2)=_
    ring
  simpa [hdef,hpack] using hxy

end GreedyBridge

section Joined
def picked (K : ℕ) (i : ℕ) : Bool := decide (i<K)

private theorem picked_count (K N : ℕ) :
    (∑ i : Fin (K+N), roundedOffset (picked K i.val)) = (K:ℤ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => roundedOffset (picked K i)), Finset.sum_range_add]
  have hh : (∑ i ∈ Finset.range K, roundedOffset (picked K i))=K := by
    calc
      _ = ∑ _i ∈ Finset.range K, (1:ℤ) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        simp [picked,roundedOffset,Finset.mem_range.mp hi]
      _ = _ := by simp
  have ht : (∑ i ∈ Finset.range N, roundedOffset (picked K (K+i)))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [picked,roundedOffset,show ¬K+i<K by omega]
  rw [hh,ht,add_zero]

private theorem picked_deficit (K N : ℕ) (c : ℕ → ℝ) :
    (∑ i : Fin (K+N), if picked K i.val then 1-(c i.val)^2 else 0) =
      (K:ℝ)-sums (fun i => (c i)^2) K := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if picked K i then 1-(c i)^2 else 0),Finset.sum_range_add]
  have hh : (∑ i ∈ Finset.range K, if picked K i then 1-(c i)^2 else 0)=
      ∑ i ∈ Finset.range K, (1-(c i)^2) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [picked,Finset.mem_range.mp hi]
  have ht : (∑ i ∈ Finset.range N, if picked K (K+i) then 1-(c (K+i))^2 else 0)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [picked,show ¬K+i<K by omega]
  rw [hh,ht,add_zero,Finset.sum_sub_distrib]
  simp [sums]

/-- The certified nearest integer offset is to round up the first K
coordinates. A threshold between the head and tail is sufficient; ties
on that threshold may be permuted. -/
private theorem nearest_integer_from_caps (K N : ℕ) (c : ℕ → ℝ) (u : ℝ)
    (hu : 0≤u) (hu1 : u≤1)
    (hc : ∀ i<K+N, 0≤c i ∧ c i≤1)
    (hhead : ∀ i<K, u≤c i) (htail : ∀ i : Fin N, c (K+i.val)≤u)
    (hfrac : sums (fun i => (c i)^2) (K+N) = (K:ℝ)) :
    let f : Fin (K+N) → ℝ := fun i => (c i.val)^2
    let d₀ : Fin (K+N) → ℤ := fun i => roundedOffset (picked K i.val)
    (∑ i, d₀ i)=(K:ℤ) ∧
    (∑ i, |(d₀ i:ℝ)-f i|)=2*((K:ℝ)-sums (fun i => (c i)^2) K) ∧
    ∀ d : Fin (K+N) → ℤ, (∑ i, d i)=(K:ℤ) →
      (∑ i, |(d₀ i:ℝ)-f i|) ≤ ∑ i, |(d i:ℝ)-f i| := by
  dsimp only
  have hf (i : Fin (K+N)) : 0≤(c i.val)^2 ∧ (c i.val)^2≤1 := by
    refine ⟨sq_nonneg _, ?_⟩
    have h := hc i.val i.isLt
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (show 0≤1+c i.val by linarith)]
  have hs : (∑ i : Fin (K+N), (c i.val)^2) =
      ∑ i : Fin (K+N), (roundedOffset (picked K i.val):ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (c i)^2)]
    change sums (fun i => (c i)^2) (K+N) = _
    rw [hfrac]
    exact_mod_cast (picked_count K N).symm
  refine ⟨picked_count K N, ?_,?_⟩
  · rw [rounded_error_eq_twice_deficit (fun i : Fin (K+N) => (c i.val)^2)
        (fun i => picked K i.val) hf hs, picked_deficit]
  · intro d hd
    apply integer_offset_minimum (fun i : Fin (K+N) => (c i.val)^2)
      (fun i => picked K i.val) d (u^2) (sq_nonneg u) ?_ hf ?_
      (hd.trans (picked_count K N).symm)
    · nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (show 0≤1+u by linarith)]
    · intro i
      by_cases h : i.val<K
      · simp only [picked, decide_eq_true_eq,h,ite_eq_left]
        have hi := hhead i.val h
        nlinarith [mul_nonneg (sub_nonneg.mpr hi) (show 0≤c i.val+u by linarith)]
      · simp [picked,h]
        let j : Fin N := ⟨i.val-K,by omega⟩
        have hj : K+j.val=i.val := by change K+(i.val-K)=i.val; omega
        have hi := htail j
        rw [hj] at hi
        nlinarith [mul_nonneg (sub_nonneg.mpr hi)
          (show 0≤c i.val+u by linarith [(hc i.val i.isLt).1])]

end Joined

section RankedPhase
/-- Same result on literal rank-normalized nonnegative integer label
counts, when the supplied integer parts and square-root residual caps
are an exact split of the rank-scaled target weights. -/
private theorem ranked_count_comparison (K N R : ℕ) (hR : 0<R)
    (c : ℕ → ℝ) (u : ℝ) (w : Fin (K+N) → ℝ) (base : Fin (K+N) → ℕ)
    (hu : 0≤u) (hu1 : u≤1)
    (hc : ∀ i<K+N, 0≤c i ∧ c i≤1)
    (hhead : ∀ i<K, u≤c i) (htail : ∀ i : Fin N, c (K+i.val)≤u)
    (hfrac : sums (fun i => (c i)^2) (K+N) = (K:ℝ))
    (hbase : (∑ i, base i)+K=R)
    (hw : ∀ i, (R:ℝ)*w i=(base i:ℝ)+(c i.val)^2) :
    let Δ := 2*((K:ℝ)-sums (fun i => (c i)^2) K)/(R:ℝ)
    let E := 2*((K:ℝ)-sums (fun i => (greedyAt c K i)^2) (K+N))/(R:ℝ)
    (∃ count : Fin (K+N) → ℕ, (∑ i, count i)=R ∧
      (∑ i, |w i-(count i:ℝ)/(R:ℝ)|)=Δ) ∧
    (∀ count : Fin (K+N) → ℕ, (∑ i, count i)=R →
      Δ≤∑ i, |w i-(count i:ℝ)/(R:ℝ)|) ∧
    ((K:ℝ)+1)/(2*(K:ℝ)+1)*Δ ≤ E ∧ E≤Δ ∧ Δ*(1-(R:ℝ)*Δ/2)≤E := by
  dsimp only
  have hpos : 0<(R:ℝ) := by exact_mod_cast hR
  let step (i : Fin (K+N)) : ℕ := if picked K i.val then 1 else 0
  let chosen : Fin (K+N) → ℕ := fun i => base i + step i
  let offset (count : Fin (K+N) → ℕ) (i : Fin (K+N)) : ℤ :=
    (count i:ℤ)-(base i:ℤ)
  have hstep (i : Fin (K+N)) : (step i:ℤ)=roundedOffset (picked K i.val) := by
    cases hi : picked K i.val <;> simp [step,roundedOffset,hi]
  have hchoose (i : Fin (K+N)) : offset chosen i=roundedOffset (picked K i.val) := by
    simp [offset,chosen,hstep]
  have hspacing (count : Fin (K+N) → ℕ) :
      (∑ i, |w i-(count i:ℝ)/(R:ℝ)|) =
        (∑ i, |(offset count i:ℝ)-(c i.val)^2|)/(R:ℝ) := by
    conv_rhs => rw [div_eq_mul_inv,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    have h : w i-(count i:ℝ)/(R:ℝ) =
        ((R:ℝ)*w i-(count i:ℝ))/(R:ℝ) := by
      field_simp [hpos.ne']
    rw [h,abs_div,abs_of_pos hpos,hw i,div_eq_mul_inv]
    congr 1
    rw [show (base i:ℝ)+(c i.val)^2-(count i:ℝ) =
          (c i.val)^2-(offset count i:ℝ) by simp [offset]; ring, abs_sub_comm]
  obtain ⟨hcnt,he,hmin⟩ := nearest_integer_from_caps K N c u hu hu1 hc hhead htail hfrac
  have hsteps : (∑ i, step i)=K := by
    have hj : (∑ i, (step i:ℤ))=(K:ℤ) := by simpa only [hstep] using hcnt
    exact_mod_cast hj
  have hc0 : (∑ i, chosen i)=R := by
    simp only [chosen,Finset.sum_add_distrib,hsteps,hbase]
  have ho (count : Fin (K+N) → ℕ) (hh : (∑ i, count i)=R) :
      (∑ i, offset count i)=(K:ℤ) := by
    have h₁ : (∑ i, (count i:ℤ))=(R:ℤ) := by exact_mod_cast hh
    have h₂ : (∑ i, (base i:ℤ))+(K:ℤ)=(R:ℤ) := by exact_mod_cast hbase
    simp only [offset, Finset.sum_sub_distrib,h₁]
    omega
  refine ⟨⟨chosen,hc0,?_⟩,?_,greedy_phase_bound K N R u c hpos hu hu1 hc hhead htail hfrac⟩
  · rw [hspacing chosen]
    simp only [hchoose]
    rw [he]
  · intro count hsum
    rw [hspacing count,← he]
    exact (div_le_div_iff_of_pos_right hpos).2 (hmin (offset count) (ho count hsum))

end RankedPhase

end RTMaxentRounding


namespace MaxEntPhase
open scoped BigOperators

/-- Algebraic data for an exact equality profile with K+3 labels.
The caps squared are K+2 copies of u² and one copy of u-u².
Its greedy prefix is K+1 copies of u, exactly exhausting the budget. -/
private theorem uniform_head_sharp_data {K : ℝ} (hK : 1 ≤ K) :
    let u := K/(K+1)
    0 < u ∧ u < 1 ∧ 0 < u-u^2 ∧ u-u^2 ≤ u^2 ∧
    (K+2)*u^2 + (u-u^2) = K ∧
    (K+1)*u = K ∧
    (K+1)*(K-K*u^2) = (2*K+1)*(K-(K+1)*u^2) ∧
    0 < K-K*u^2 := by
  dsimp only
  have hpos : 0 < K+1 := by linarith
  let u := K/(K+1)
  change 0 < u ∧ u < 1 ∧ 0 < u-u^2 ∧ u-u^2 ≤ u^2 ∧
    (K+2)*u^2 + (u-u^2) = K ∧ (K+1)*u = K ∧
    (K+1)*(K-K*u^2) = (2*K+1)*(K-(K+1)*u^2) ∧ 0 < K-K*u^2
  have hu : (K+1)*u = K := by dsimp [u]; field_simp
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : u < 1 := (div_lt_iff₀ hpos).2 (by linarith)
  have huhalf : (1:ℝ)/2 ≤ u := (le_div_iff₀ hpos).2 (by linarith)
  have hp := mul_pos hu0 (sub_pos.mpr hu1)
  have hq := mul_nonneg hu0.le (show 0 ≤ 2*u-1 by linarith)
  have hq2 := mul_pos (show 0 < K by linarith)
    (mul_pos (sub_pos.mpr hu1) (show 0 < 1+u by positivity))
  have hid : (K+2)*u^2 + (u-u^2) = K := by
    calc
      _ = ((K+1)*u)*u + u := by ring
      _ = (K+1)*u := by calc
        ((K+1)*u)*u + u = K*u + u := by rw [hu]
        _ = (K+1)*u := by ring
      _ = K := hu
  have heq : (K+1)*(K-K*u^2) = (2*K+1)*(K-(K+1)*u^2) := by
    calc
      _ = (2*K+1)*(K-(K+1)*u^2) + ((K+1)*u)^2 - K^2 := by ring
      _ = _ := by rw [hu]; ring
  exact ⟨hu0, hu1, by nlinarith only [hp], by nlinarith only [hq],
    hid, hu, heq, by nlinarith only [hq2]⟩

end MaxEntPhase

namespace MaxEntPhase
open RTMaxentRounding

noncomputable def familyCaps (K : ℕ) (i : ℕ) : ℝ :=
  let u := (K:ℝ)/((K:ℝ)+1)
  if i<K+2 then u else Real.sqrt (u-u^2)

private theorem sums_const_on {f : ℕ → ℝ} {n : ℕ} {a : ℝ} (h : ∀ i<n, f i=a) :
    sums f n=(n:ℝ)*a := by
  unfold sums
  calc
    _ = ∑ _i ∈ Finset.range n, a := Finset.sum_congr rfl (fun i hi => h i (Finset.mem_range.mp hi))
    _ = _ := by simp

/-- The exact lower factor is attained for every positive phase K by a
strict fractional-cap profile with K+3 labels. -/
private theorem sharp_fractional_family (K : ℕ) (hK : 1≤K) (r : ℝ) (hr : 0<r) :
    let c := familyCaps K
    let Δ := 2*((K:ℝ)-sums (fun i => (c i)^2) K)/r
    let E := 2*((K:ℝ)-sums (fun i => (greedyAt c K i)^2) (K+3))/r
    (∀ i<K+3, 0≤c i ∧ c i<1) ∧
    sums (fun i => (c i)^2) (K+3)=(K:ℝ) ∧
    (∀ i j, i≤j → c j≤c i) ∧
    0<Δ ∧ ((K:ℝ)+1)/(2*(K:ℝ)+1)*Δ = E := by
  let u := (K:ℝ)/((K:ℝ)+1)
  let c := familyCaps K
  change (∀ i<K+3, 0≤c i ∧ c i<1) ∧
    sums (fun i => (c i)^2) (K+3)=(K:ℝ) ∧
    (∀ i j, i≤j → c j≤c i) ∧
    0<2*((K:ℝ)-sums (fun i => (c i)^2) K)/r ∧
    ((K:ℝ)+1)/(2*(K:ℝ)+1)*(2*((K:ℝ)-sums (fun i => (c i)^2) K)/r) =
      2*((K:ℝ)-sums (fun i => (greedyAt c K i)^2) (K+3))/r
  have hKr : (1:ℝ)≤K := by exact_mod_cast hK
  obtain ⟨hu0,hu1,hv0,hvu,hm,hu,heq,hD⟩ := uniform_head_sharp_data hKr
  change 0<u at hu0
  change u<1 at hu1
  change 0<u-u^2 at hv0
  change u-u^2≤u^2 at hvu
  change ((K:ℝ)+2)*u^2+(u-u^2)=K at hm
  change ((K:ℝ)+1)*u=K at hu
  change ((K:ℝ)+1)*((K:ℝ)-(K:ℝ)*u^2) =
    (2*(K:ℝ)+1)*((K:ℝ)-((K:ℝ)+1)*u^2) at heq
  change 0<(K:ℝ)-(K:ℝ)*u^2 at hD
  let v := Real.sqrt (u-u^2)
  have hv : v≤u := (Real.sqrt_le_left hu0.le).2 hvu
  have hvn : 0≤v := Real.sqrt_nonneg _
  have hvs : v^2=u-u^2 := Real.sq_sqrt hv0.le
  have c_eq (i : ℕ) : c i = if i<K+2 then u else v := rfl
  have c_pre (i : ℕ) (hi : i<K+2) : c i=u := by rw [c_eq,ite_eq_left hi]
  have c_end : c (K+2)=v := by rw [c_eq,ite_eq_right (by omega)]
  have pre (n : ℕ) (hn : n≤K+2) : sums c n=(n:ℝ)*u :=
    sums_const_on fun i hi => c_pre i (lt_of_lt_of_le hi hn)
  have pre_sq (n : ℕ) (hn : n≤K+2) : sums (fun i => (c i)^2) n=(n:ℝ)*u^2 :=
    sums_const_on fun i hi => by rw [c_pre i (lt_of_lt_of_le hi hn)]
  have fall (i j : ℕ) (hij : i≤j) : c j≤c i := by
    rw [c_eq,c_eq]
    split_ifs with hj hi hi
    · rfl
    · omega
    · exact hv
    · rfl
  have gpre (i : ℕ) (hi : i<K+1) : greedyAt c K i=u := by
    have hir0 : (i:ℝ) ≤ (K:ℝ) := by exact_mod_cast (show i≤K by omega)
    have hir : (i:ℝ)+1 ≤ (K:ℝ)+1 := by linarith
    have hiu := mul_le_mul_of_nonneg_right hir hu0.le
    unfold greedyAt
    rw [c_pre i (by omega),pre i (by omega)]
    apply min_eq_left
    apply le_trans _ (le_max_right _ _)
    nlinarith only [hiu,hu]
  have gpost (i : ℕ) (hi : K + 1 ≤ i) : greedyAt c K i=0 := by
    have hS : (K:ℝ)≤sums c i := by
      have hS' : sums c (K+1)≤sums c i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi)
        intro j _ _
        rw [c_eq]
        split_ifs <;> first | exact hu0.le | exact hvn
      rw [pre (K+1) (by omega),Nat.cast_add,Nat.cast_one,hu] at hS'
      exact hS'
    unfold greedyAt
    rw [max_eq_left (sub_nonpos.mpr hS),min_eq_right]
    rw [c_eq]
    split_ifs <;> first | exact hu0.le | exact hvn
  have gsum : sums (fun i => (greedyAt c K i)^2) (K+3)=((K:ℝ)+1)*u^2 := by
    change sums (fun i => (greedyAt c K i)^2) ((K+1)+2)=_
    unfold sums
    rw [Finset.sum_range_add]
    have hh : (∑ i ∈ Finset.range (K+1), (greedyAt c K i)^2)=((K:ℝ)+1)*u^2 := by
      change sums (fun i => (greedyAt c K i)^2) (K+1)=_
      rw [sums_const_on (a:=u^2) (fun i hi => by rw [gpre i hi]),Nat.cast_add,Nat.cast_one]
    have hz : (∑ i ∈ Finset.range 2, (greedyAt c K (K+1+i))^2) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [gpost _ (by omega)]
      norm_num
    rw [hh,hz,add_zero]
  refine ⟨?_,?_,fall,?_,?_⟩
  · intro i _
    rw [c_eq]
    split_ifs
    · exact ⟨hu0.le,hu1⟩
    · exact ⟨hvn,hv.trans_lt hu1⟩
  · rw [show sums (fun i => (c i)^2) (K+3) =
      sums (fun i => (c i)^2) (K+2)+(c (K+2))^2 from
        Finset.sum_range_succ (fun i => (c i)^2) (K+2)]
    rw [pre_sq _ le_rfl,c_end,hvs,Nat.cast_add]
    norm_num
    exact hm
  · rw [pre_sq K (by omega)]
    exact div_pos (mul_pos (by norm_num) hD) hr
  · rw [pre_sq K (by omega),gsum]
    have hden : (2*(K:ℝ)+1) ≠ 0 := by positivity
    field_simp
    linarith only [heq]

end MaxEntPhase

open scoped BigOperators
open RTMaxentRounding MaxEntPhase

/-- The literal greedy packing loss of the residual square-root capacities. -/
noncomputable def packingError (K m : ℕ) (r : ℝ) (c : ℕ → ℝ) : ℝ :=
  2 * ((K:ℝ) - sums (fun i => (greedyAt c K i)^2) m) / r

/-- Exact scalar comparison, including positive-error sharpness for every
positive integer phase. The channel attainment problem is not a premise
or a conclusion here. -/
def PhaseLaw (K : ℕ) (observe : ℕ → ℝ → (ℕ → ℝ) → ℝ) : Prop :=
  (∀ (N R : ℕ) (_hR : 0<R)
    (c : ℕ → ℝ) (u : ℝ) (w : Fin (K+N) → ℝ) (base : Fin (K+N) → ℕ),
    0≤u → u≤1 →
    (∀ i<K+N, 0≤c i ∧ c i≤1) →
    (∀ i<K, u≤c i) → (∀ i : Fin N, c (K+i.val)≤u) →
    sums (fun i => (c i)^2) (K+N) = (K:ℝ) →
    (∑ i, base i)+K=R →
    (∀ i, (R:ℝ)*w i=(base i:ℝ)+(c i.val)^2) →
    let Δ := 2*((K:ℝ)-sums (fun i => (c i)^2) K)/(R:ℝ)
    let E := observe (K+N) R c
    (∃ count : Fin (K+N) → ℕ, (∑ i, count i)=R ∧
      (∑ i, |w i-(count i:ℝ)/(R:ℝ)|)=Δ) ∧
    (∀ count : Fin (K+N) → ℕ, (∑ i, count i)=R →
      Δ≤∑ i, |w i-(count i:ℝ)/(R:ℝ)|) ∧
    ((K:ℝ)+1)/(2*(K:ℝ)+1)*Δ ≤ E ∧ E≤Δ ∧ Δ*(1-(R:ℝ)*Δ/2)≤E) ∧
  (1≤K → ∀ r : ℝ, 0<r → ∃ c : ℕ → ℝ,
    let Δ := 2*((K:ℝ)-sums (fun i => (c i)^2) K)/r
    (∀ i<K+3, 0≤c i ∧ c i<1) ∧
    sums (fun i => (c i)^2) (K+3)=(K:ℝ) ∧
    (∀ i j, i≤j → c j≤c i) ∧
    0<Δ ∧ ((K:ℝ)+1)/(2*(K:ℝ)+1)*Δ = observe (K+3) r c)

/-- The sharp fixed-phase factor connects the exact closest rank-count
partition and the actual greedy cap packing. The stated fixed-K constant
is optimal, not merely asymptotically approached. -/
theorem phase_rounding :
    ∀ K : ℕ, let observed := packingError K; PhaseLaw K observed := by
  intro K
  refine ⟨?_,?_⟩
  · intro N R hR c u w base hu hu1 hc hhead htail hfrac hbase hw
    exact ranked_count_comparison K N R hR c u w base hu hu1 hc hhead htail hfrac hbase hw
  · intro hK r hr
    exact ⟨familyCaps K, sharp_fractional_family K hK r hr⟩

#print axioms phase_rounding
end D5.S3.Quantum.Entanglement.SectorChannels.MaxentRankPhaseRounding
