/- GID: D5/S3/Arith/Primes/CubicProbeFourierBudget
   generality: G
   mirror-B: D5/B/S3/Arith/Primes/CubicProbeFourierBudget
   mirror-E: none(waiver:independent-cubic-coordinate-budget)
   anchors: []
   utility: none
   digest: Exact normalized Fourier-mass budget for cubic split and nonsplit observations forcing long periods. -/

import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Dedup
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
The opposite-lag construction uses the nonsimply-bordered partial-word
argument of Blanchet-Sadri, Allen, Byrum and Mercaş (LATA 2009, Theorem 1).
The cyclic cubic filters have different normalized Fourier costs; the
weighted budget combines these with the finite-horizon design. No
Galois independence or analytic prime bound is asserted here.
-/
namespace D5.S3.Arith.Primes.CubicProbeFourierBudget


/-- Every lag at most P is realized by a difference from the initial
interval of length a to a later sampled multiple of a or to the endpoint P. -/
private theorem sparseDifference (a P d : Nat) (ha : 0 < a) (hd : 0 < d) (hP : d ≤ P) :
    ∃ j < a, j + d ≤ P ∧ (j+d = P ∨ ∃ k, 0 < k ∧ j+d = k*a) := by
  let q := (d-1)/a
  let k := q+1
  have hr : (d-1)%a < a := Nat.mod_lt _ ha
  have he : q*a + (d-1)%a = d-1 := by
    simpa [q,Nat.mul_comm] using Nat.div_add_mod (d-1) a
  have hk : k*a = q*a+a := by simp [k,Nat.add_mul]
  have hlo : d ≤ k*a := by omega
  have hhi : k*a < d+a := by omega
  by_cases h : k*a ≤ P
  · refine ⟨k*a-d,by omega,h |> Nat.le_trans (by omega),Or.inr ⟨k,by simp [k],by omega⟩⟩
  · refine ⟨P-d,by omega,by omega,Or.inl (by omega)⟩

def Period (s : Nat → Bool) (d : Nat) : Prop := ∀ i, s (i+d) = s i

private def Samples (left right : List Nat) (s : Nat → Bool) : Prop :=
  (∀ i ∈ left, s i = true) ∧ ∀ i ∈ right, s i = false

private def Dist (a b : Nat) : Nat := max a b - min a b

private def OppositeLags (left right : List Nat) (P : Nat) : Prop :=
  ∀ k, P/2 < k → k ≤ P → ∃ a ∈ left, ∃ b ∈ right, Dist a b = k

private theorem upper_multiple (P d : Nat) (hd : 0<d) (hle : d≤P) :
    ∃ k, P/2 < k ∧ k ≤ P ∧ d∣k := by
  let q := P/d
  let k := d*q
  have hq : 0 < q := Nat.div_pos hle hd
  have hk : d ≤ k := by
    simpa [k] using Nat.mul_le_mul_left d (show 1≤q by omega)
  have he : k + P%d = P := by
    simpa [k,q,Nat.mul_comm] using Nat.div_add_mod P d
  have hr : P%d < d := Nat.mod_lt _ hd
  refine ⟨k,by omega,by omega,⟨q,rfl⟩⟩

private theorem period_mul {s : Nat → Bool} {d : Nat} (h : Period s d) (m : Nat) :
    Period s (d*m) := by
  intro i
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, h, ih]

private theorem no_sample_clash {left right : List Nat} {s : Nat → Bool}
    (hs : Samples left right s) {d a b : Nat} (hper : Period s d)
    (ha : a ∈ left) (hb : b ∈ right) (hdiv : d∣Dist a b) : False := by
  obtain ⟨m,hm⟩ := hdiv
  have hp := period_mul hper m
  have hne : s a ≠ s b := by rw [hs.1 a ha, hs.2 b hb]; decide
  by_cases h : a≤b
  · have he : a+d*m=b := by unfold Dist at hm; omega
    exact hne ((hp a).symm.trans (congrArg s he))
  · have he : b+d*m=a := by unfold Dist at hm; omega
    exact hne ((congrArg s he).symm.trans (hp b))

private theorem upper_lags_suffice {left right : List Nat} {P : Nat}
    (hlag : OppositeLags left right P) {s : Nat → Bool} (hs : Samples left right s)
    {d : Nat} (hd : 0<d) (hper : Period s d) : P<d := by
  by_cases h : d≤P
  · obtain ⟨k,hk,hle,hdiv⟩ := upper_multiple P d hd h
    obtain ⟨a,ha,b,hb,he⟩ := hlag k hk hle
    exact (no_sample_clash hs hper ha hb (he ▸ hdiv)).elim
  · omega

private theorem dist_div_of_eq_mod {a b d : Nat} (h : a%d = b%d) : d∣Dist a b := by
  have ha := Nat.div_add_mod a d
  have hb := Nat.div_add_mod b d
  by_cases hab : a≤b
  · have he : Dist a b = d*(b/d-a/d) := by
      unfold Dist
      rw [Nat.max_eq_right hab,Nat.min_eq_left hab,Nat.mul_sub_left_distrib]
      omega
    exact ⟨_,he⟩
  · have hba : b≤a := by omega
    have he : Dist a b = d*(a/d-b/d) := by
      unfold Dist
      rw [Nat.max_eq_left hba,Nat.min_eq_right hba,Nat.mul_sub_left_distrib]
      omega
    exact ⟨_,he⟩

private def periodicCompletion (left : List Nat) (d i : Nat) : Bool :=
  left.any (fun a => a % d == i % d)

private theorem completion_period (left : List Nat) (d : Nat) :
    Period (periodicCompletion left d) d := by
  intro i
  unfold periodicCompletion
  congr 1
  funext a
  rw [Nat.add_mod_right]

private theorem completion_samples {left right : List Nat} {d : Nat}
    (h : ∀ a ∈ left, ∀ b ∈ right, ¬ d∣Dist a b) :
    Samples left right (periodicCompletion left d) := by
  constructor
  · intro i hi
    exact List.any_eq_true.mpr ⟨i,hi,by simp⟩
  · intro i hi
    cases he : periodicCompletion left d i with
    | false => rfl
    | true =>
      obtain ⟨a,ha,hm⟩ := List.any_eq_true.mp he
      have hh : a%d = i%d := by simpa using hm
      exact (h a ha i hi (dist_div_of_eq_mod hh)).elim

/-- Exact characterization of partial Boolean samples in a fixed horizon
that force the period to exceed the horizon. Only upper-half lags need
direct clashes; lower lags are excluded by taking multiples. Conversely,
a missing upper-half lag gives a periodic completion with that period. -/
private theorem force_iff_upper_lags (left right : List Nat) (P : Nat)
    (hleft : ∀ a ∈ left, a ≤ P) (hright : ∀ b ∈ right, b ≤ P)
    (hdisj : ∀ a ∈ left, a ∉ right) :
    (∀ s : Nat → Bool, Samples left right s →
      ∀ d, 0<d → Period s d → P<d) ↔ OppositeLags left right P := by
  constructor
  · intro hforce k hk hle
    apply Classical.byContradiction
    intro habs
    have hn : ∀ a ∈ left, ∀ b ∈ right, ¬ k∣Dist a b := by
      intro a ha b hb hv
      have Hleft := hleft a ha
      have Hright := hright b hb
      have hne : a ≠ b := by
        intro he
        exact hdisj a ha (he ▸ hb)
      obtain ⟨m,hm⟩ := hv
      have hpos : 0 < Dist a b := by unfold Dist; omega
      have hbound : Dist a b ≤ P := by unfold Dist; omega
      have hm1 : m=1 := by
        by_cases hzero : m=0
        · simp [hzero] at hm; omega
        · by_cases hs : m=1
          · exact hs
          · have hm2 : 2≤m := by omega
            have ht := Nat.mul_le_mul_left k hm2
            omega
      exact habs ⟨a,ha,b,hb,by simpa [hm1] using hm⟩
    have hf := hforce _ (completion_samples hn) k (by omega) (completion_period left k)
    omega
  · intro h s hs d hd hp
    exact upper_lags_suffice h hs hd hp

/-- The upper-half grid uses only the final half of the previous
single-step interval. The grid observations are at floor(P/2)+k*a. -/
private theorem upper_grid_forces (s : Nat → Bool) (a P : Nat) (ha : 0<a)
    (hfirst : ∀ i<a, s i = true)
    (hgrid : ∀ k, 0<k → P/2+k*a≤P → s (P/2+k*a) = false)
    (hend : s P = false) (d : Nat) (hd : 0<d) (hper : Period s d) : P<d := by
  by_cases hh : d≤P
  · obtain ⟨k,hk,hkP,hdiv⟩ := upper_multiple P d hd hh
    let t := k-P/2
    have ht : 0<t := by omega
    have htP : t ≤ P-P/2 := by omega
    obtain ⟨j,hj,hjP,hs⟩ := sparseDifference a (P-P/2) t ha ht htP
    have hleft := hfirst j hj
    have hright : s (j+k) = false := by
      rcases hs with he | ⟨m,hm,he⟩
      · have hv : j+k=P := by omega
        rw [hv]
        exact hend
      · have hv : j+k=P/2+m*a := by omega
        rw [hv]
        exact hgrid m hm (by omega)
    obtain ⟨m,hm⟩ := hdiv
    have hshift := period_mul hper m j
    rw [← hm,hleft] at hshift
    rw [hright] at hshift
    contradiction
  · omega

def Force (A B : Finset Nat) (P : Nat) : Prop :=
  ∀ s : Nat → Bool, (∀ a ∈ A, s a = true) → (∀ b ∈ B, s b = false) →
    ∀ d, 0<d → Period s d → P<d

private theorem upper_lag_product_lower (A B : Finset Nat) (P : Nat)
    (hA : ∀ a∈A, a≤P) (hB : ∀ b∈B, b≤P)
    (hdisj : Disjoint A B) (h : Force A B P) :
    P-P/2 ≤ A.card*B.card := by
  have hforce (s : Nat → Bool) (hs : Samples A.toList B.toList s) :
      ∀ d, 0<d → Period s d → P<d :=
    h s (fun a ha => hs.1 a (Finset.mem_toList.mpr ha))
      (fun b hb => hs.2 b (Finset.mem_toList.mpr hb))
  have hg := (force_iff_upper_lags A.toList B.toList P
    (fun a ha => hA a (Finset.mem_toList.mp ha))
    (fun b hb => hB b (Finset.mem_toList.mp hb))
    (fun a ha hb => Finset.disjoint_left.mp hdisj (Finset.mem_toList.mp ha) (Finset.mem_toList.mp hb))).mp hforce
  have hcover : Finset.Ioc (P/2) P ⊆ (A ×ˢ B).image (fun t => Dist t.1 t.2) := by
    intro k hk
    have hk' := Finset.mem_Ioc.mp hk
    obtain ⟨a,ha,b,hb,he⟩ := hg k hk'.1 hk'.2
    exact Finset.mem_image.mpr ⟨(a,b),
      Finset.mem_product.mpr ⟨Finset.mem_toList.mp ha,Finset.mem_toList.mp hb⟩,he⟩
  calc
    P-P/2 = (Finset.Ioc (P/2) P).card := (Nat.card_Ioc _ _).symm
    _ ≤ ((A ×ˢ B).image (fun t => Dist t.1 t.2)).card := Finset.card_le_card hcover
    _ ≤ (A ×ˢ B).card := Finset.card_image_le
    _ = A.card * B.card := Finset.card_product _ _

/-- Opposite-label budgets can be capped separately, rather than balanced. -/
private theorem forcing_with_caps (P a₀ b : Nat) (hP : 0<P) :
  (∃ A B : Finset Nat,
      (∀ a∈A, a≤P) ∧ (∀ a∈B, a≤P) ∧ Disjoint A B ∧
        A.card≤a₀ ∧ B.card≤b ∧ Force A B P) ↔ P-P/2≤a₀*b := by
  constructor
  · rintro ⟨A,B,hA,hB,hD,ha,hb,hf⟩
    exact (upper_lag_product_lower A B P hA hB hD hf).trans (Nat.mul_le_mul ha hb)
  · intro h
    let H := P-P/2
    let a := min a₀ H
    have hH : 0<H := by dsimp [H]; omega
    have ha₀ : 0<a₀ := by
      by_cases hz : a₀=0
      · rw [hz,Nat.zero_mul] at h
        omega
      · omega
    have ha : 0<a := by dsimp [a]; omega
    have hb : 0<b := by
      by_cases hz : b=0
      · rw [hz,Nat.mul_zero] at h
        omega
      · omega
    have hw : H≤a*b := by
      by_cases hh : a₀≤H
      · simpa only [a,Nat.min_eq_left hh] using (show H≤a₀*b from h)
      · dsimp [a]
        rw [Nat.min_eq_right (by omega : H≤a₀)]
        simpa using Nat.mul_le_mul_left H (show 1≤b by omega)
    let A : Finset Nat := Finset.range a
    let loc (k : Nat) := min P (P/2+k*a)
    let B : Finset Nat := (Finset.Ioc 0 b).image loc
    have hA (i : Nat) (hi : i∈A) : i<a := Finset.mem_range.mp hi
    have hB (i : Nat) (hi : i∈B) : P/2 < i ∧ i≤P := by
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hi
      have hkp := (Finset.mem_Ioc.mp hk).1
      have hka : a ≤ k*a := by
        simpa using Nat.mul_le_mul_right a (show 1≤k by omega)
      dsimp [loc]
      omega
    have hcA : A.card=a := Finset.card_range a
    have hcB : B.card≤b := by
      calc
        B.card ≤ (Finset.Ioc 0 b).card := Finset.card_image_le
        _ = b := by simp
    refine ⟨A,B,fun i hi=>by have := hA i hi; dsimp [a,H] at this; omega,
      fun i hi=>(hB i hi).2,Finset.disjoint_left.mpr ?_, hcA.trans_le (Nat.min_le_left _ _), hcB, ?_⟩
    · intro i hia hib
      have hia' := hA i hia
      have hib' := (hB i hib).1
      dsimp [a,H] at hia'
      omega
    · intro s hsA hsB d hd hper
      apply upper_grid_forces s a P ha (fun i hi => hsA i (Finset.mem_range.mpr hi)) ?_ ?_ d hd hper
      · intro k hk hka
        have hkH : k*a≤H := by dsimp [H]; omega
        have hkb : k≤b := Nat.le_of_mul_le_mul_right (by rw [Nat.mul_comm b a]; exact hkH.trans hw) ha
        have hh : loc k = P/2+k*a := Nat.min_eq_right hka
        apply hsB
        rw [← hh]
        exact Finset.mem_image.mpr ⟨k,Finset.mem_Ioc.mpr ⟨hk,hkb⟩,rfl⟩
      · have he : loc b = P := by
          unfold loc
          rw [Nat.min_eq_left]
          rw [Nat.mul_comm b a]
          dsimp [H] at hw
          omega
        apply hsB
        rw [← he]
        exact Finset.mem_image.mpr ⟨b,Finset.mem_Ioc.mpr ⟨hb,le_rfl⟩,rfl⟩

/-- Sharp feasible set for a multiplicatively weighted split/nonsplit budget. -/
private theorem forcing_weighted_iff (P M c₀ c₁ : Nat) (hP : 0<P)
    (hc₀ : 1≤c₀) (hc₁ : 1≤c₁) :
    (∃ A B : Finset Nat,
      (∀ a∈A, a≤P) ∧ (∀ b∈B, b≤P) ∧ Disjoint A B ∧
      c₀^A.card*c₁^B.card≤M ∧ Force A B P) ↔
    ∃ a b : Nat, P-P/2≤a*b ∧ c₀^a*c₁^b≤M := by
  constructor
  · rintro ⟨A,B,hA,hB,hd,hm,hf⟩
    exact ⟨A.card,B.card,upper_lag_product_lower A B P hA hB hd hf,hm⟩
  · rintro ⟨a,b,h,hm⟩
    obtain ⟨A,B,hA,hB,hd,ha,hb,hf⟩ := (forcing_with_caps P a b hP).mpr h
    have hcA := Nat.pow_le_pow_right (by omega : 0<c₀) ha
    have hcB := Nat.pow_le_pow_right (by omega : 0<c₁) hb
    exact ⟨A,B,hA,hB,hd,(Nat.mul_le_mul hcA hcB).trans hm,hf⟩

/-- The actual cubic acceptance table: identity alone or its complement. -/
private def value (s : Bool) (i : Fin 3) : Rat :=
  if (i == 0) == s then 1 else 0

/-- The last two acceptance values coincide. For a nontrivial character
the conjugate sum at nonidentity elements is −1, while for the trivial
character it is 2. This computes the common off-diagonal coefficient
directly from the signed acceptance table. -/
private def main (s : Bool) : Rat := (value s 0+value s 1+value s 2)/3

private def off (s : Bool) : Rat := ((value s 0-value s 1)/3) / main s

private theorem off_value (s : Bool) : off s = if s then 1 else -1/2 := by
  cases s <;> decide +kernel


/-- Exact enumerator for the normalized product-character coefficients of
independent cubic coordinates, in lexicographic tensor order. -/
private def coeffs : List Bool → List Rat
  | [] => [1]
  | s::ss =>
    let cs := coeffs ss
    cs ++ cs.map (fun a=>off s*a) ++ cs.map (fun a=>off s*a)

private def l1 (ss : List Bool) : Rat := ((coeffs ss).map abs).sum

private theorem l1_factor (s : Bool) (ss : List Bool) :
    l1 (s::ss) = (1+2*|off s|)*l1 ss := by
  simp only [l1, coeffs, List.map_append, List.sum_append, List.map_map,
    Function.comp_def, abs_mul, List.sum_map_mul_left]
  ring

/-- This ratio is exactly 3 per prescribed split and 2 per prescribed
nonsplit, not 3 per prescribed exact ternary symbol. -/
private theorem l1_exact (ss : List Bool) :
    l1 ss = 3^(ss.count true)*2^(ss.count false) := by
  induction ss with
  | nil => norm_num [l1, coeffs]
  | cons s ss ih =>
    cases s <;> rw [l1_factor, ih] <;>
      simp [off_value, pow_succ] <;> ring

private def layout (a b : Nat) : List Bool :=
  List.replicate a true ++ List.replicate b false

private theorem l1_layout (a b : Nat) : l1 (layout a b) = 3^a*2^b := by
  rw [l1_exact]
  simp [layout, List.count_append, List.count_replicate]

/-- Actual normalized sum of absolute product-character coefficients,
computed from the identity and nonidentity cubic acceptance filters. -/
def fourierCharge (a b : Nat) : Rat := l1 (layout a b)

/-- Sharp normalized Fourier budget for forcing long periods, when split
and nonsplit restrictions independently live on cubic coordinates.
No analytic prime bound or independence theorem is a premise of this
combinatorial/finite harmonic statement. -/
theorem cubic_fourier_budget_iff (P M : Nat) (hP : 0<P) :
    (∃ A B : Finset Nat,
      (∀ a∈A, a≤P) ∧ (∀ b∈B, b≤P) ∧ Disjoint A B ∧
      fourierCharge A.card B.card ≤ (M : Rat) ∧ Force A B P) ↔
    ∃ a b : Nat, P-P/2≤a*b ∧ 3^a*2^b≤M := by
  have hc (a b : Nat) : fourierCharge a b ≤ (M : Rat) ↔ 3^a*2^b≤M := by
    rw [fourierCharge, l1_layout]
    exact_mod_cast (Iff.rfl : (3^a*2^b≤M) ↔ (3^a*2^b≤M))
  have ht := forcing_weighted_iff P M 3 2 hP (by decide) (by decide)
  constructor
  · rintro ⟨A,B,hA,hB,hD,hw,hF⟩
    exact ht.mp ⟨A,B,hA,hB,hD,(hc _ _).mp hw,hF⟩
  · intro h
    obtain ⟨A,B,hA,hB,hD,hw,hF⟩ := ht.mpr h
    exact ⟨A,B,hA,hB,hD,(hc _ _).mpr hw,hF⟩

end D5.S3.Arith.Primes.CubicProbeFourierBudget
