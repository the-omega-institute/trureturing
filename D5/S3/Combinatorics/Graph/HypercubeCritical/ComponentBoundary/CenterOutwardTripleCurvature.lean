/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleCurvature
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleCurvature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Negative Huang square curvature obstructs a cancelling triple of closed single-active-private-coordinate residuals. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CenterOutwardWeightGauge

/-! The three-center curvature obstruction for the actual Huang signing in arbitrary
dimension. The application is to Hong–Wu–Xia, arXiv:2610.09483v1, Section 7,
Problem 2. All residual coefficients are real. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CenterOutwardTripleCurvature

open scoped BigOperators
open BalancedCriticalSpectrum (Q flip_apply_same gamma_apply)
local notation "flip" => BalancedCriticalSpectrum.flip
open BalancedCubeGirth (flip_comm)
open CenterOutwardDifference (outward)
open CenterOutwardWeightGauge (supportedKernel)
open private edge edge_sq edge_curvature edge_reciprocal from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

private theorem flip_apply_of_ne {n : ℕ} (r : Q n) {i j : Fin n} (h : j ≠ i) :
    flip r i j = r j :=
  Function.update_of_ne h _ _

private theorem bool_not_ne_self (b : Bool) : (!b) ≠ b := by
  cases b <;> decide

private theorem bool_not_eq_of_ne {b d : Bool} (h : b ≠ d) : (!b) = d := by
  cases b <;> cases d <;> simp_all

private theorem edge_ne_zero {n : ℕ} (r : Q n) (i : Fin n) : edge r i ≠ 0 := by
  intro h
  have hs := edge_sq r i
  rw [h] at hs
  norm_num at hs

private theorem outward_eq_edge_sum {n : ℕ} (w : Fin n → ℝ) (d : Q n)
    (v : Q n → ℝ) (r : Q n) :
    outward w d v r =
      ∑ i, w i * (if r i ≠ d i then edge r i * v (flip r i) else 0) := by
  simp only [outward, gamma_apply, edge]

/-- A closed weighted residual supported on the center side of one nonzero-weight
coordinate is zero. The outward equation at the flipped row isolates that
coordinate's contribution. No assumptions on the other weights are needed. -/
theorem closed_eq_zero_of_fixed_center_bit {n : ℕ} (w : Fin n → ℝ)
    (d : Q n) (v : Q n → ℝ) (i : Fin n) (hwi : w i ≠ 0)
    (hclosed : outward w d v = 0)
    (hsupp : ∀ r, v r ≠ 0 → r i = d i) : v = 0 := by
  funext r
  change v r = 0
  by_contra hr
  let q := flip r i
  have hqi : q i ≠ d i := by
    dsimp only [q]
    rw [flip_apply_same, hsupp r hr]
    exact bool_not_ne_self (d i)
  let f (j : Fin n) : ℝ :=
    w j * (if q j ≠ d j then edge q j * v (flip q j) else 0)
  have hsum : (∑ j, f j) = 0 := by
    have h := congrFun hclosed q
    change outward w d v q = 0 at h
    simpa only [outward_eq_edge_sum, f] using h
  have hrest (j : Fin n) (hji : j ≠ i) : f j = 0 := by
    have hv : v (flip q j) = 0 := by
      by_contra hn
      exact hqi ((flip_apply_of_ne q hji.symm).symm.trans (hsupp _ hn))
    simp [f, hv]
  have hsingle : (∑ j, f j) = f i :=
    Finset.sum_eq_single i (fun j _ hj => hrest j hj) (by simp)
  rw [hsingle] at hsum
  have hflip : flip q i = r := BalancedCriticalSpectrum.flip_flip r i
  have hterm : w i * (edge q i * v r) = 0 := by
    simpa only [f, if_pos hqi, hflip] using hsum
  exact hr ((mul_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left hwi)).resolve_left
    (edge_ne_zero q i))

/-- The fixed-center-bit obstruction expressed using the supported kernel of
the weighted outward operator. -/
theorem supportedKernel_eq_zero_of_fixed_center_bit {n : ℕ} (w : Fin n → ℝ)
    (d : Q n) (S : Set (Q n)) (v : Q n → ℝ) (i : Fin n) (hwi : w i ≠ 0)
    (hS : ∀ r ∈ S, r i = d i) (hv : v ∈ supportedKernel w d S) : v = 0 := by
  change (∀ r ∉ S, v r = 0) ∧ outward w d v = 0 at hv
  apply closed_eq_zero_of_fixed_center_bit w d v i hwi hv.2
  intro r hr
  by_cases h : r ∈ S
  · exact hS r h
  · exact (hr (hv.1 r h)).elim

/-- Each nonzero row has exactly one coordinate in the private union `P`
whose bit differs from the majority `m`. This coordinate is outside the
residual's own private block `D`. Coordinates outside `P` are unrestricted. -/
def SingleActiveSupport {n : ℕ} (m : Q n) (P D : Finset (Fin n))
    (v : Q n → ℝ) : Prop :=
  ∀ r, v r ≠ 0 →
    ∃ k ∈ P, k ∉ D ∧ r k ≠ m k ∧ ∀ l ∈ P, l ≠ k → r l = m l

/-- At any base agreeing with the majority on the private union, two distinct
private axes outside a closed residual's own block have equal normalized
coefficients. Multiplication by `edge F i` is division by the sign of the
edge from `flip F i` to `F`, since the actual Huang signs are reciprocal
and square to one. -/
theorem closed_single_active_edge_relation {n : ℕ} (m d : Q n)
    (P D : Finset (Fin n)) (v : Q n → ℝ) (F : Q n) {i j : Fin n}
    (hcenter : ∀ l, d l ≠ m l ↔ l ∈ D)
    (hclosed : outward (fun _ => 1) d v = 0)
    (hs : SingleActiveSupport m P D v)
    (hF : ∀ l ∈ P, F l = m l)
    (hi : i ∈ P) (hj : j ∈ P) (hiD : i ∉ D) (hjD : j ∉ D)
    (hij : i ≠ j) :
    edge F i * v (flip F i) = edge F j * v (flip F j) := by
  classical
  let q := flip (flip F i) j
  have hqi : q i = !(m i) := by
    dsimp only [q]
    rw [flip_apply_of_ne (flip F i) hij, flip_apply_same, hF i hi]
  have hqj : q j = !(m j) := by
    dsimp only [q]
    rw [flip_apply_same, flip_apply_of_ne F hij.symm, hF j hj]
  have hdi : d i = m i := by
    by_contra h
    exact hiD ((hcenter i).mp h)
  have hdj : d j = m j := by
    by_contra h
    exact hjD ((hcenter j).mp h)
  have hqdi : q i ≠ d i := by
    rw [hqi, hdi]
    exact bool_not_ne_self (m i)
  have hqdj : q j ≠ d j := by
    rw [hqj, hdj]
    exact bool_not_ne_self (m j)
  have hflipi : flip q i = flip F j := by
    dsimp only [q]
    rw [flip_comm (flip F i) j i, BalancedCriticalSpectrum.flip_flip]
  have hflipj : flip q j = flip F i := BalancedCriticalSpectrum.flip_flip (flip F i) j
  -- Any other flip retains both active private coordinates i and j.
  have hrest (l : Fin n) (hli : l ≠ i) (hlj : l ≠ j) : v (flip q l) = 0 := by
    by_contra hn
    obtain ⟨k, _, _, _, hkrest⟩ := hs (flip q l) hn
    have hacti : flip q l i ≠ m i := by
      rw [flip_apply_of_ne q hli.symm, hqi]
      exact bool_not_ne_self (m i)
    have hactj : flip q l j ≠ m j := by
      rw [flip_apply_of_ne q hlj.symm, hqj]
      exact bool_not_ne_self (m j)
    have hki : k = i := by
      by_contra h
      exact hacti (hkrest i hi (Ne.symm h))
    have hkj : k = j := by
      by_contra h
      exact hactj (hkrest j hj (Ne.symm h))
    exact hij (hki.symm.trans hkj)
  let f (l : Fin n) : ℝ :=
    if q l ≠ d l then edge q l * v (flip q l) else 0
  have hsum : (∑ l, f l) = 0 := by
    have h := congrFun hclosed q
    change outward (fun _ => 1) d v q = 0 at h
    simpa only [outward_eq_edge_sum, one_mul, f] using h
  have hpair : (∑ l, f l) = f i + f j := by
    calc
      _ = ∑ l ∈ ({i, j} : Finset (Fin n)), f l := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro l _ hl
        have hli : l ≠ i := fun e => hl (by simp [e])
        have hlj : l ≠ j := fun e => hl (by simp [e])
        simp [f, hrest l hli hlj]
      _ = _ := Finset.sum_pair hij
  rw [hpair] at hsum
  have hrow : edge q i * v (flip F j) + edge q j * v (flip F i) = 0 := by
    simpa only [f, if_pos hqdi, if_pos hqdj, hflipi, hflipj] using hsum
  have hrow' : edge q j * v (flip F i) = -(edge q i * v (flip F j)) := by
    linarith only [hrow]
  -- The two signs at the double-flip corner are reciprocal to the
  -- corresponding signs in the negative Huang square based at F.
  have hrecj : edge q j = edge (flip F i) j :=
    edge_reciprocal (flip F i) j
  have hreci : edge q i = edge (flip F j) i := by
    dsimp only [q]
    rw [flip_comm F i j, edge_reciprocal]
  have hcurv : edge F i * edge q j = -(edge F j * edge q i) := by
    rw [hrecj, hreci]
    exact edge_curvature F hij
  calc
    edge F i * v (flip F i) =
        edge F i * edge q j ^ 2 * v (flip F i) := by rw [edge_sq, mul_one]
    _ = (edge F i * edge q j) * (edge q j * v (flip F i)) := by ring
    _ = (-(edge F j * edge q i)) * (-(edge q i * v (flip F j))) := by
      rw [hcurv, hrow']
    _ = edge F j * edge q i ^ 2 * v (flip F j) := by ring
    _ = edge F j * v (flip F j) := by rw [edge_sq, mul_one]

private theorem zero_on_own_axis {n : ℕ} (m : Q n) (P D : Finset (Fin n))
    (v : Q n → ℝ) (hs : SingleActiveSupport m P D v)
    (F : Q n) (hF : ∀ l ∈ P, F l = m l)
    (i : Fin n) (hi : i ∈ P) (hiD : i ∈ D) : v (flip F i) = 0 := by
  by_contra hn
  obtain ⟨k, _, hkD, _, hkrest⟩ := hs (flip F i) hn
  have hact : flip F i i ≠ m i := by
    rw [flip_apply_same, hF i hi]
    exact bool_not_ne_self (m i)
  by_cases hki : k = i
  · subst k
    exact hkD hiD
  · exact hact (hkrest i hi (Ne.symm hki))

/-- Vanishing on the single-flip rows over every majority base exhausts the
possible nonzero rows under the private-coordinate support hypothesis. -/
private theorem eq_zero_of_single_active_rows {n : ℕ} (m : Q n)
    (P D : Finset (Fin n)) (v : Q n → ℝ) (hs : SingleActiveSupport m P D v)
    (hrows : ∀ F : Q n, (∀ l ∈ P, F l = m l) →
      ∀ i ∈ P, v (flip F i) = 0) : v = 0 := by
  funext r
  change v r = 0
  by_contra hr
  obtain ⟨i, hi, _, hact, hrest⟩ := hs r hr
  have hbase : ∀ l ∈ P, flip r i l = m l := by
    intro l hl
    by_cases hli : l = i
    · subst l
      rw [flip_apply_same]
      exact bool_not_eq_of_ne hact
    · rw [flip_apply_of_ne r hli]
      exact hrest l hl hli
  exact hr (by simpa only [BalancedCriticalSpectrum.flip_flip] using hrows (flip r i) hbase i hi)

/-- Three nonempty, pairwise disjoint private blocks determine three centers
relative to their majority. If each residual is closed at its own center,
the residuals cancel, and each nonzero row has exactly one active private
coordinate outside its residual's own block, then all residuals vanish.

For each base in the common private-zero fiber and every triple of directions
(one per block), the three square equations identify the normalized values
on the two allowed axes of each residual. Cancellation at the three
single-flip rows forces their values to be zero. -/
theorem closed_triple_single_active_eq_zero {n : ℕ} (m a b c : Q n)
    (A B C : Finset (Fin n))
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (ha : ∀ i, a i ≠ m i ↔ i ∈ A)
    (hb : ∀ i, b i ≠ m i ↔ i ∈ B)
    (hc : ∀ i, c i ≠ m i ↔ i ∈ C)
    (x y z : Q n → ℝ)
    (hx : outward (fun _ => 1) a x = 0)
    (hy : outward (fun _ => 1) b y = 0)
    (hz : outward (fun _ => 1) c z = 0)
    (hcancel : x + y + z = 0)
    (hxs : SingleActiveSupport m (A ∪ B ∪ C) A x)
    (hys : SingleActiveSupport m (A ∪ B ∪ C) B y)
    (hzs : SingleActiveSupport m (A ∪ B ∪ C) C z) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  classical
  let P := A ∪ B ∪ C
  have hAP : A ⊆ P := by
    intro t ht
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ht)))
  have hBP : B ⊆ P := by
    intro t ht
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ht)))
  have hCP : C ⊆ P := by
    intro t ht
    exact Finset.mem_union.mpr (Or.inr ht)
  change SingleActiveSupport m P A x at hxs
  change SingleActiveSupport m P B y at hys
  change SingleActiveSupport m P C z at hzs
  have htriangle (F : Q n) (hF : ∀ l ∈ P, F l = m l)
      (i j k : Fin n) (hi : i ∈ A) (hj : j ∈ B) (hk : k ∈ C) :
      (x (flip F i) = 0 ∧ y (flip F i) = 0 ∧ z (flip F i) = 0) ∧
      (x (flip F j) = 0 ∧ y (flip F j) = 0 ∧ z (flip F j) = 0) ∧
      (x (flip F k) = 0 ∧ y (flip F k) = 0 ∧ z (flip F k) = 0) := by
    have hiB : i ∉ B := fun h => Finset.disjoint_left.mp hAB hi h
    have hiC : i ∉ C := fun h => Finset.disjoint_left.mp hAC hi h
    have hjA : j ∉ A := fun h => Finset.disjoint_left.mp hAB h hj
    have hjC : j ∉ C := fun h => Finset.disjoint_left.mp hBC hj h
    have hkA : k ∉ A := fun h => Finset.disjoint_left.mp hAC h hk
    have hkB : k ∉ B := fun h => Finset.disjoint_left.mp hBC h hk
    have hij : i ≠ j := fun e => hjA (e ▸ hi)
    have hik : i ≠ k := fun e => hkA (e ▸ hi)
    have hjk : j ≠ k := fun e => hkB (e ▸ hj)
    have hiP := hAP hi
    have hjP := hBP hj
    have hkP := hCP hk
    have hxi := zero_on_own_axis m P A x hxs F hF i hiP hi
    have hyj := zero_on_own_axis m P B y hys F hF j hjP hj
    have hzk := zero_on_own_axis m P C z hzs F hF k hkP hk
    have hxrel :=
      closed_single_active_edge_relation m a P A x F ha hx hxs hF hjP hkP hjA hkA hjk
    have hyrel :=
      closed_single_active_edge_relation m b P B y F hb hy hys hF hiP hkP hiB hkB hik
    have hzrel :=
      closed_single_active_edge_relation m c P C z F hc hz hzs hF hiP hjP hiC hjC hij
    have normalized_cancel (t : Fin n) :
        edge F t * x (flip F t) + edge F t * y (flip F t) +
          edge F t * z (flip F t) = 0 := by
      have h := congrFun hcancel (flip F t)
      change x (flip F t) + y (flip F t) + z (flip F t) = 0 at h
      calc
        _ = edge F t * (x (flip F t) + y (flip F t) + z (flip F t)) := by ring
        _ = 0 := by rw [h, mul_zero]
    have hci := normalized_cancel i
    rw [hxi, mul_zero, zero_add] at hci
    have hcj := normalized_cancel j
    rw [hyj, mul_zero, add_zero] at hcj
    have hck := normalized_cancel k
    rw [hzk, mul_zero, add_zero] at hck
    have cancel_edge (t : Fin n) (s : ℝ) (h : edge F t * s = 0) : s = 0 :=
      (mul_eq_zero.mp h).resolve_left (edge_ne_zero F t)
    refine ⟨⟨hxi, cancel_edge i _ ?_, cancel_edge i _ ?_⟩,
      ⟨cancel_edge j _ ?_, hyj, cancel_edge j _ ?_⟩,
      ⟨cancel_edge k _ ?_, cancel_edge k _ ?_, hzk⟩⟩ <;>
      linarith only [hxrel, hyrel, hzrel, hci, hcj, hck]
  obtain ⟨i, hi⟩ := hA
  obtain ⟨j, hj⟩ := hB
  obtain ⟨k, hk⟩ := hC
  have hrows (F : Q n) (hF : ∀ l ∈ P, F l = m l)
      (t : Fin n) (ht : t ∈ P) :
      x (flip F t) = 0 ∧ y (flip F t) = 0 ∧ z (flip F t) = 0 := by
    change t ∈ A ∪ B ∪ C at ht
    rcases Finset.mem_union.mp ht with htAB | htC
    · rcases Finset.mem_union.mp htAB with htA | htB
      · exact (htriangle F hF t j k htA hj hk).1
      · exact (htriangle F hF i t k hi htB hk).2.1
    · exact (htriangle F hF i j t hi hj htC).2.2
  exact ⟨eq_zero_of_single_active_rows m P A x hxs (fun F hF t ht => (hrows F hF t ht).1),
    eq_zero_of_single_active_rows m P B y hys (fun F hF t ht => (hrows F hF t ht).2.1),
    eq_zero_of_single_active_rows m P C z hzs (fun F hF t ht => (hrows F hF t ht).2.2)⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CenterOutwardTripleCurvature
