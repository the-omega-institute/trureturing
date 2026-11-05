/- GID: D5/S1/Dynamics/Shadowing/ReturnDistanceShadowing
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/ReturnDistanceShadowing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Natural-time two-point tracing in compact two-sided return-distance subshifts. -/

import D5.S1.Dynamics.Shadowing.ReturnDistanceSubshift
import D5.S1.Dynamics.Shadowing.MetricTracing
import Mathlib.Order.Filter.Bases.Finite

/-! Finite-set tracing uses the same nonempty set at every natural time and bounds
its initial diameter. The countable product metric has the actual product uniformity. -/

open Set Function Filter SymbolicDynamics.FullShift
open scoped PiCountable Uniformity

namespace D5.S1.Dynamics.Shadowing

/-- Original neighborhood two-shadowing, expressed with nonempty finite sets and
actual distance to the image set. -/
def NeighborhoodTwoShadowing {X : Type*} [MetricSpace X] (f : X → X) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ z : ℕ → X, MetricPseudoOrbit f δ z →
    ∃ A : Finset X, A.Nonempty ∧ A.card ≤ 2 ∧ Metric.diam (A : Set X) < ε ∧
      ∀ i, Metric.infDist (z i) (f^[i] '' (A : Set X)) < ε

/-- Two fixed witnesses give the original finite-set contract, including diameter
and nonempty set-distance. Coincident witnesses are permitted. -/
theorem neighborhood_two_of_pair {X : Type*} [MetricSpace X] {f : X → X}
    (h : ∀ ε > 0, ∃ δ > 0, ∀ z : ℕ → X, MetricPseudoOrbit f δ z →
      ∃ a b : X, dist a b < ε ∧
        ∀ i, dist (f^[i] a) (z i) < ε ∨ dist (f^[i] b) (z i) < ε) :
    NeighborhoodTwoShadowing f := by
  classical
  intro ε hε
  obtain ⟨δ, hδ, ht⟩ := h ε hε
  refine ⟨δ, hδ, fun z hz => ?_⟩
  obtain ⟨a, b, hab, ht⟩ := ht z hz
  refine ⟨{a, b}, by simp, ?_, ?_, ?_⟩
  · exact (Finset.card_insert_le a {b}).trans (by simp)
  · simpa only [Finset.coe_pair, Metric.diam_pair] using hab
  · intro i
    simp only [Finset.coe_pair]
    have hn : (f^[i] '' ({a, b} : Set X)).Nonempty := ⟨f^[i] a, a, by simp, rfl⟩
    apply (Metric.infDist_lt_iff hn).mpr
    rcases ht i with ha | hb
    · exact ⟨f^[i] a, ⟨a, by simp, rfl⟩, by simpa only [dist_comm] using ha⟩
    · exact ⟨f^[i] b, ⟨b, by simp, rfl⟩, by simpa only [dist_comm] using hb⟩

/-- A finite set of integer coordinates fits in a symmetric finite window. -/
theorem finite_integer_window {S : Set ℤ} (hS : S.Finite) :
    ∃ r : ℕ, ∀ j ∈ S, -(r : ℤ) ≤ j ∧ j ≤ r := by
  obtain ⟨u, hu⟩ := hS.bddAbove
  obtain ⟨l, hl⟩ := hS.bddBelow
  refine ⟨u.natAbs + l.natAbs, fun j hj => ?_⟩
  have hju := hu hj
  have hlj := hl hj
  have hau : u ≤ u.natAbs := Int.le_natAbs
  have hal : -(l.natAbs : ℤ) ≤ l := by
    have ht : -l ≤ ((-l).natAbs : ℤ) := Int.le_natAbs
    simp only [Int.natAbs_neg] at ht
    omega
  constructor <;> omega

/-- Agreement on a sufficiently large signed window implies metric closeness.
The metric here is Mathlib's compatible countable product metric. -/
theorem return_metric_window (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, ∀ x y : ℤ → ReturnBit,
      (∀ j : ℤ, -(r : ℤ) ≤ j → j ≤ r → x j = y j) → dist x y < ε := by
  have hu : 𝓤 (ℤ → ReturnBit) =
      ⨅ j : ℤ, 𝓟 {xy : (ℤ → ReturnBit) × (ℤ → ReturnBit) | xy.1 j = xy.2 j} := by
    rw [Pi.uniformity]
    simp_rw [DiscreteUniformity.eq_principal_setRelId, Filter.comap_principal]
    rfl
  have he := Metric.dist_mem_uniformity (α := ℤ → ReturnBit) hε
  rw [hu] at he
  obtain ⟨S, hS, hsub⟩ := (hasBasis_iInf_principal_finite
    (fun j : ℤ => {xy : (ℤ → ReturnBit) × (ℤ → ReturnBit) | xy.1 j = xy.2 j})).mem_iff.mp he
  obtain ⟨r, hr⟩ := finite_integer_window hS
  refine ⟨r, fun x y hxy => hsub (a := (x, y)) ?_⟩
  simp only [mem_iInter, mem_setOf_eq]
  intro j hj
  exact hxy j (hr j hj).1 (hr j hj).2

/-- Strict small metric errors force equality on any prescribed signed window. -/
theorem return_window_control (K : ℕ) :
    ∃ δ > 0, ∀ x y : ℤ → ReturnBit, dist x y < δ →
      ∀ j : ℤ, -(K : ℤ) ≤ j → j ≤ K → x j = y j := by
  have he (j : ℤ) : {xy : (ℤ → ReturnBit) × (ℤ → ReturnBit) | xy.1 j = xy.2 j}
      ∈ 𝓤 (ℤ → ReturnBit) :=
    (Pi.uniformContinuous_proj (fun _ : ℤ => ReturnBit) j)
      (DiscreteUniformity.relId_mem_uniformity ReturnBit)
  have hE := (Filter.biInter_mem (Set.finite_Icc (-(K : ℤ)) K)).mpr
    (fun j _ => he j)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_uniformity_dist.mp hE
  refine ⟨δ, hδ, fun x y hxy j hjl hju => ?_⟩
  exact mem_iInter.mp (mem_iInter.mp (hsub hxy) j) ⟨hjl, hju⟩

/-- Extend only the past of a natural-time sequence by the exact orbit of its initial point. -/
def pastExtension {A : Type*} (z : ℕ → ℤ → A) (i : ℤ) : ℤ → A :=
  if 0 ≤ i then z i.toNat else shift i (z 0)

/-- The diagonal retains negative initial coordinates. -/
def signedDiagonal {A : Type*} (z : ℕ → ℤ → A) (j : ℤ) : A :=
  pastExtension z j 0

theorem past_extension_overlap {A : Type*} {z : ℕ → ℤ → A} {K : ℕ}
    (h : ∀ i : ℕ, ∀ j : ℤ, -(K : ℤ) ≤ j → j ≤ K →
      z i (j + 1) = z (i + 1) j) :
    ∀ i j : ℤ, -(K : ℤ) ≤ j → j ≤ K →
      pastExtension z i (j + 1) = pastExtension z (i + 1) j := by
  intro i j hjl hju
  by_cases hi : 0 ≤ i
  · have hip : 0 ≤ i + 1 := by omega
    simp only [pastExtension, if_pos hi, if_pos hip]
    have hc : (i + 1).toNat = i.toNat + 1 := by omega
    rw [hc]
    exact h i.toNat j hjl hju
  · by_cases hip : 0 ≤ i + 1
    · have hie : i = -1 := by omega
      subst i
      simp [pastExtension, shift_apply]
    · simp only [pastExtension, if_neg hi, if_neg hip, shift_apply]
      congr 1
      omega

/-- Signed overlap, with natural-time observations and exact past extension. -/
theorem signed_diagonal_overlap {A : Type*} {z : ℕ → ℤ → A} {K : ℕ}
    (h : ∀ i : ℕ, ∀ j : ℤ, -(K : ℤ) ≤ j → j ≤ K →
      z i (j + 1) = z (i + 1) j) :
    ∀ (i : ℤ) (j : ℤ), -(K : ℤ) ≤ j → j ≤ K →
      signedDiagonal z (i + j) = pastExtension z i j := by
  intro i j
  induction j using Int.induction_on generalizing i with
  | zero => intro _ _; simp [signedDiagonal]
  | succ n ih =>
    intro hjl hju
    have hh := ih (i + 1) (by omega) (by omega)
    have he := past_extension_overlap h i (n : ℤ) (by omega) (by omega)
    convert hh.trans he.symm using 1 <;> congr 1 <;> omega
  | pred n ih =>
    intro hjl hju
    have hh := ih (i - 1) (by omega) (by omega)
    have he := past_extension_overlap h (i - 1) (-(n : ℤ) - 1) hjl hju
    have he' : pastExtension z (i - 1) (-(n : ℤ)) =
        pastExtension z i (-(n : ℤ) - 1) := by simpa using he
    convert hh.trans he' using 1 <;> congr 1 <;> omega

/-- Iteration of the restricted shift reads the genuine integer coordinate. -/
theorem return_shift_iterate (D : Set ℤ) (x : ReturnPoint D) (i : ℕ) (j : ℤ) :
    ((returnShift D)^[i] x).1 j = x.1 ((i : ℤ) + j) := by
  induction i generalizing x j with
  | zero => simp
  | succ i ih =>
    rw [iterate_succ_apply, ih]
    change x.1 (1 + ((i : ℤ) + j)) = x.1 ((↑(i + 1) : ℤ) + j)
    have he : 1 + ((i : ℤ) + j) = ((i + 1 : ℕ) : ℤ) + j := by omega
    rw [he]

/-- Equality of the one indicators determines the binary symbol. -/
theorem return_bit_ext {a b : ReturnBit} (h : (a = returnOne ↔ b = returnOne)) : a = b := by
  apply Subtype.ext
  have ha := a.property
  have hb := b.property
  have hone (c : ReturnBit) : c = returnOne ↔ c.val = 1 := by
    exact ⟨fun he => congrArg Subtype.val he, fun he => Subtype.ext he⟩
  rw [hone, hone] at h
  simp only [Finset.mem_range] at ha hb
  omega

/-- Unbounded positive allowed distances, in a form suited to finite windows. -/
def UnboundedReturnDistances (D : Set ℤ) : Prop :=
  ∀ N : ℕ, ∃ h : ℕ, N < h ∧ (h : ℤ) ∈ D

/-- The same interval repair provides two fixed tracers for every positive-return
set containing one and arbitrarily large positive distances. -/
theorem unbounded_return_neighborhood_two {D : Set ℤ} (hone : (1 : ℤ) ∈ D)
    (hunbounded : UnboundedReturnDistances D) : NeighborhoodTwoShadowing (returnShift D) := by
  classical
  apply neighborhood_two_of_pair
  intro ε hε
  obtain ⟨r, hεr⟩ := return_metric_window ε hε
  obtain ⟨h, hhr, hhD⟩ := hunbounded (2 * r)
  let K := 2 * h
  have hrK : r ≤ K := by dsimp [K]; omega
  have hpos : (0 : ℤ) < h := by omega
  obtain ⟨δ, hδ, hδK⟩ := return_window_control K
  refine ⟨δ, hδ, fun z hz => ?_⟩
  let zz : ℕ → ℤ → ReturnBit := fun i => (z i).1
  have hedge : ∀ i : ℕ, ∀ j : ℤ, -(K : ℤ) ≤ j → j ≤ K →
      zz i (j + 1) = zz (i + 1) j := by
    intro i j hjl hju
    simpa [zz, shift_apply, add_comm] using
      hδK (shift 1 (z i).1) (z (i + 1)).1 (hz i) j hjl hju
  let c := signedDiagonal zz
  have hc (i : ℕ) (j : ℤ) (hjl : -(K : ℤ) ≤ j) (hju : j ≤ K) :
      c ((i : ℤ) + j) = (z i).1 j := by
    simpa [c, pastExtension] using signed_diagonal_overlap hedge (i : ℤ) j hjl hju
  let P := oneSupport c ∩ Set.Ici (-(r : ℤ))
  have hshort : ∀ p q, SupportAdjacent P p q → q - p ≤ K → q - p ∈ D := by
    intro p q hpq hlen
    have hpl : -(r : ℤ) ≤ p := hpq.1.2
    have hpone : c p = returnOne := hpq.1.1
    have hqone : c q = returnOne := hpq.2.1.1
    have hpqlt := hpq.2.2.1
    let i : ℕ := (max p 0).toNat
    have hi : (i : ℤ) = max p 0 := by dsimp [i]; omega
    have hpi : -(K : ℤ) ≤ p - i := by omega
    have hqi : q - i ≤ K := by omega
    have hw (t : ℤ) (hpt : p ≤ t) (htq : t ≤ q) :
        c t = (z i).1 (t - i) := by
      have he := hc i (t - i) (by omega) (by omega)
      simpa using he
    have hadj : SupportAdjacent (oneSupport (z i).1) (p - i) (q - i) := by
      refine ⟨?_, ?_, by omega, ?_⟩
      · change (z i).1 (p - i) = returnOne
        rw [← hw p le_rfl (by omega)]
        exact hpone
      · change (z i).1 (q - i) = returnOne
        rw [← hw q (by omega) le_rfl]
        exact hqone
      · intro t hpt htq ht
        apply hpq.2.2.2 (t + i) (by omega) (by omega)
        refine ⟨?_, by change -(r : ℤ) ≤ t + i; omega⟩
        change c (t + i) = returnOne
        rw [hw (t + i) (by omega) (by omega)]
        simpa [oneSupport] using ht
    have hd := (z i).2 (p - i) (q - i) hadj
    simpa using hd
  let R := repairedSupport D P (h : ℤ)
  let B := P ∩ Set.Icc (-(r : ℤ)) r
  have haLegal : ReturnLegal D (supportPoint R) := by
    intro p q hpq
    rw [one_support_point] at hpq
    exact repaired_support_legal hpos hone hhD
      (fun p q hpq hle => hshort p q hpq (by simpa [K] using hle)) p q hpq
  have hbLegal : ReturnLegal D (supportPoint B) := by
    intro p q hpq
    rw [one_support_point] at hpq
    exact truncated_support_legal (fun p q hpq hle => hshort p q hpq (by omega)) p q hpq
  let a : ReturnPoint D := ⟨supportPoint R, haLegal⟩
  let b : ReturnPoint D := ⟨supportPoint B, hbLegal⟩
  have ha0 (t : ℤ) (htl : -(r : ℤ) ≤ t) (htu : t ≤ r) : a.1 t = c t := by
    apply return_bit_ext
    change (supportPoint R t = returnOne ↔ c t = returnOne)
    change (t ∈ oneSupport (supportPoint R) ↔ t ∈ oneSupport c)
    rw [one_support_point]
    constructor
    · rintro (ht | ht)
      · exact ht.1
      · obtain ⟨p, q, hpq, _, hpt, _⟩ := ht
        have hpl : -(r : ℤ) ≤ p := hpq.1.2
        omega
    · intro ht
      exact Or.inl ⟨ht, htl⟩
  have hb0 (t : ℤ) (htl : -(r : ℤ) ≤ t) (htu : t ≤ r) : b.1 t = c t := by
    apply return_bit_ext
    change (t ∈ oneSupport (supportPoint B) ↔ t ∈ oneSupport c)
    rw [one_support_point]
    exact ⟨fun ht => ht.1.1, fun ht => ⟨⟨ht, htl⟩, htl, htu⟩⟩
  refine ⟨a, b, ?_, ?_⟩
  · exact hεr a.1 b.1 (fun t htl htu => (ha0 t htl htu).trans (hb0 t htl htu).symm)
  · intro i
    by_cases hwindow : ∃ s ∈ P, (i : ℤ) - r ≤ s ∧ s ≤ (i : ℤ) + r
    · left
      apply hεr
      intro j hjl hju
      rw [return_shift_iterate]
      rw [← hc i j (by omega) (by omega)]
      apply return_bit_ext
      change ((i : ℤ) + j ∈ oneSupport (supportPoint R) ↔
        (i : ℤ) + j ∈ oneSupport c)
      rw [one_support_point]
      exact (repaired_window_eq (by omega) hwindow _ (by omega) (by omega)).trans
        ⟨fun ht => ht.1, fun ht => ⟨ht, by change -(r : ℤ) ≤ (i : ℤ) + j; omega⟩⟩
    · right
      apply hεr
      intro j hjl hju
      rw [return_shift_iterate]
      rw [← hc i j (by omega) (by omega)]
      apply return_bit_ext
      change ((i : ℤ) + j ∈ oneSupport (supportPoint B) ↔
        (i : ℤ) + j ∈ oneSupport c)
      rw [one_support_point]
      constructor
      · exact fun ht => ht.1.1
      · intro ht
        exact (hwindow ⟨(i : ℤ) + j, ⟨ht, by change -(r : ℤ) ≤ (i : ℤ) + j; omega⟩,
          by omega, by omega⟩).elim

#print axioms unbounded_return_neighborhood_two
#print axioms return_metric_window
#print axioms return_window_control
#print axioms signed_diagonal_overlap

end D5.S1.Dynamics.Shadowing
