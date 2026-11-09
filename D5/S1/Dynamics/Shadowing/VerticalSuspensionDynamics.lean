/- GID: D5/S1/Dynamics/Shadowing/VerticalSuspensionDynamics
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/VerticalSuspensionDynamics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Artanh, mathlib/module/Mathlib.Topology.Constructions]
   utility: none
   digest: Signed quotient infrastructure for the full integer vertical suspension crossing selector. -/

import D5.S1.Dynamics.Shadowing.VerticalSuspensionGeometry

/-! Full integer pseudo-orbits and the crossing interpolation domain. -/

noncomputable section

open Set Function Topology Filter

namespace D5.S1.Dynamics.Shadowing.VerticalSuspensionSelector

variable {K : Type*} [TopologicalSpace K]

structure LocalEquiconnection (K : Type*) [TopologicalSpace K] where
  domain : Set (K × K)
  isOpen_domain : IsOpen domain
  diagonal : ∀ u, (u, u) ∈ domain
  connect : domain × Set.Icc (0 : ℝ) 1 → K
  continuous_connect : Continuous connect
  left : ∀ p : domain, connect (p, ⟨0, by constructor <;> norm_num⟩) = p.1.1
  right : ∀ p : domain, connect (p, ⟨1, by constructor <;> norm_num⟩) = p.1.2
  refl : ∀ u t, connect (⟨(u, u), diagonal u⟩, t) = u

/-- All integers and non-strict errors, with the inherited full product topology. -/
abbrev ClosedPseudoOrbit {X : Type*} [PseudoMetricSpace X] (f : X → X) (δ : ℝ) :=
  {x : ℤ → X // ∀ j : ℤ, dist (f (x j)) (x (j + 1)) ≤ δ}

theorem closed_pseudoOrbit {X : Type*} [PseudoMetricSpace X]
    {f : X → X} (hf : Continuous f) (δ : ℝ) :
    IsClosed {x : ℤ → X | ∀ j : ℤ, dist (f (x j)) (x (j + 1)) ≤ δ} := by
  simp only [ofPred_forall]
  apply isClosed_iInter (fun j => ?_)
  exact isClosed_le ((hf.comp (continuous_apply j)).dist (continuous_apply (j + 1)))
    continuous_const

/-- Translation by any integer stays on exactly the same closed domain. -/
def shift {X : Type*} [PseudoMetricSpace X] (f : X → X) (δ : ℝ) (n : ℤ) :
    ClosedPseudoOrbit f δ ≃ₜ ClosedPseudoOrbit f δ where
  toFun x := ⟨fun j => x.1 (j + n), fun j => by
    simpa only [add_assoc, add_comm, add_left_comm] using x.2 (j + n)⟩
  invFun x := ⟨fun j => x.1 (j - n), fun j => by
    simpa only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using x.2 (j - n)⟩
  left_inv x := by ext j; simp
  right_inv x := by ext j; simp
  continuous_toFun := (continuous_pi (fun j =>
    (continuous_apply (j + n)).comp
      (continuous_subtype_val : Continuous (fun x : ClosedPseudoOrbit f δ => x.1)))).subtype_mk _
  continuous_invFun := (continuous_pi (fun j =>
    (continuous_apply (j - n)).comp
      (continuous_subtype_val : Continuous (fun x : ClosedPseudoOrbit f δ => x.1)))).subtype_mk _

theorem shift_zpow {X : Type*} [PseudoMetricSpace X] (f : X → X)
    (δ : ℝ) (n : ℤ) : (shift f δ 1) ^ n = shift f δ n := by
  induction n using Int.induction_on with
  | zero =>
    ext x j
    simp [shift]
  | succ n ih =>
    rw [zpow_add, zpow_one, ih]
    ext x j
    change x.1 ((j + (n : ℤ)) + 1) = x.1 (j + ((n : ℤ) + 1))
    rw [add_assoc]
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -(n : ℤ) + -1 by omega, zpow_add, zpow_neg_one, ih]
    ext x j
    change x.1 ((j + -(n : ℤ)) - 1) = x.1 (j + (-(n : ℤ) + -1))
    simp only [sub_eq_add_neg, add_assoc]

/-- The weak crossing convention retains both charts at a zero seam. -/
def Crossing (v : ℤ → ℝ) (j : ℤ) : Prop := v j ≤ 0 ∧ 0 ≤ v (j + 1)

def ForwardSign (v : ℤ → ℝ) : Prop := ∀ j, 0 ≤ v j → 0 < v (j + 1)

theorem nonnegative_after {v : ℤ → ℝ} (hv : ForwardSign v)
    {i j : ℤ} (hij : i ≤ j) (hi : 0 ≤ v i) : 0 ≤ v j := by
  have hn : ∀ n : ℕ, 0 ≤ v (i + n) := by
    intro n
    induction n with
    | zero => simpa using hi
    | succ n ih => simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using (hv _ ih).le
  have he : i + ((j - i).toNat : ℤ) = j := by
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hij)]
    ring
  simpa only [he] using hn (j - i).toNat

theorem positive_after {v : ℤ → ℝ} (hv : ForwardSign v)
    {i j : ℤ} (hij : i < j) (hi : 0 ≤ v i) : 0 < v j := by
  have hp := hv (j - 1) (nonnegative_after hv (show i ≤ j - 1 by omega) hi)
  simpa using hp

theorem negative_before {v : ℤ → ℝ} (hv : ForwardSign v)
    {i j : ℤ} (hij : i < j) (hj : v j ≤ 0) : v i < 0 := by
  by_contra hi
  exact (not_lt_of_ge hj) (positive_after hv hij (le_of_not_gt hi))

theorem crossing_classification {v : ℤ → ℝ} (hv : ForwardSign v) :
    (∀ j, v j < 0) ∨ (∀ j, 0 < v j) ∨ ∃ j, Crossing v j := by
  classical
  by_cases hn : ∀ j, v j < 0
  · exact Or.inl hn
  right
  by_cases hp : ∀ j, 0 < v j
  · exact Or.inl hp
  right
  push_neg at hn hp
  obtain ⟨s, hs⟩ := hn
  obtain ⟨r, hr⟩ := hp
  by_cases hz : v r = 0
  · exact ⟨r, hz.le, (hv r hz.ge).le⟩
  have hr' : v r < 0 := lt_of_le_of_ne hr hz
  obtain ⟨k, hk, hmin⟩ := Int.exists_least_of_bdd
    (P := fun k => 0 ≤ v k)
    ⟨r, by
      intro k hk
      by_contra hkr
      have := nonnegative_after hv (show k ≤ r by omega) hk
      linarith⟩ ⟨s, hs⟩
  refine ⟨k - 1, ?_, by simpa using hk⟩
  have hneg : v (k - 1) < 0 := by
    by_contra h
    have := hmin (k - 1) (le_of_not_gt h)
    omega
  exact hneg.le

theorem crossing_separation {v : ℤ → ℝ} (hv : ForwardSign v)
    {i j : ℤ} (hi : Crossing v i) (hj : Crossing v j) :
    i = j ∨ (i + 1 = j ∧ v j = 0) ∨ (j + 1 = i ∧ v i = 0) := by
  have hupper : j ≤ i + 1 := by
    by_contra h
    have := positive_after hv (show i + 1 < j by omega) hi.2
    linarith [hj.1]
  have hlower : i ≤ j + 1 := by
    by_contra h
    have := positive_after hv (show j + 1 < i by omega) hj.2
    linarith [hi.1]
  rcases lt_trichotomy i j with h | h | h
  · right; left
    have he : i + 1 = j := by omega
    exact ⟨he, le_antisymm hj.1 (he ▸ hi.2)⟩
  · exact Or.inl h
  · right; right
    have he : j + 1 = i := by omega
    exact ⟨he, le_antisymm hi.1 (he ▸ hj.2)⟩

theorem crossing_local_range {v : ℤ → ℝ} (hv : ForwardSign v)
    {a b j : ℤ} (ha : v a < 0) (hb : 0 < v b) (hj : Crossing v j) :
    a ≤ j ∧ j < b := by
  constructor
  · by_contra h
    have := nonnegative_after hv (show j + 1 ≤ a by omega) hj.2
    linarith
  · by_contra h
    have := nonnegative_after hv (show b ≤ j by omega) hb.le
    rcases eq_or_lt_of_le (show b ≤ j by omega) with he | he
    · subst j
      linarith [hj.1]
    · have := positive_after hv he hb.le
      linarith [hj.1]

theorem continuous_artanh_interior :
    Continuous (fun v : Ioo (-1 : ℝ) 1 => Real.artanh v) := by
  have he : (fun v : Ioo (-1 : ℝ) 1 => Real.artanh v) =
      fun v : Ioo (-1 : ℝ) 1 => (1 / 2 : ℝ) * Real.log ((1 + (v : ℝ)) / (1 - (v : ℝ))) := by
    funext v
    exact Real.artanh_eq_half_log ⟨v.2.1.le, v.2.2.le⟩
  rw [he]
  apply continuous_const.mul
  apply Continuous.log
  · exact (continuous_const.add continuous_subtype_val).div
      (continuous_const.sub continuous_subtype_val) (fun v => by linarith [v.2.2])
  · intro v
    exact ne_of_gt (div_pos (by linarith [v.2.1]) (by linarith [v.2.2]))

/-- This contains interior and W checks, rather than postulating a selector. -/
structure ValidCrossing (H : LocalEquiconnection K) (z w : Suspension K) : Prop where
  left_interior : (height z : ℝ) ∈ Ioo (-1 : ℝ) 1
  right_interior : (height w : ℝ) ∈ Ioo (-1 : ℝ) 1
  labels : (label ⟨z, left_interior⟩, label ⟨w, right_interior⟩) ∈ H.domain

/-- An auxiliary full-history domain used to assemble the explicit formula.
The compact link bound maps every admitted metric pseudoorbit into this domain. -/
abbrev AdmissibleHistory (H : LocalEquiconnection K) :=
  {x : ℤ → Suspension K //
    ForwardSign (fun j => (height (x j) : ℝ)) ∧
    ∀ j, Crossing (fun k => (height (x k) : ℝ)) j → ValidCrossing H (x j) (x (j + 1))}

def historyHeight {H : LocalEquiconnection K} (x : AdmissibleHistory H) (j : ℤ) : ℝ :=
  height (x.1 j)

def crossingFraction {H : LocalEquiconnection K} (x : AdmissibleHistory H)
    (j : ℤ) : ℝ :=
  -Real.artanh (historyHeight x j) /
    (Real.artanh (historyHeight x (j + 1)) - Real.artanh (historyHeight x j))

theorem crossingFraction_mem {H : LocalEquiconnection K}
    (x : AdmissibleHistory H) (j : ℤ) (hj : Crossing (historyHeight x) j) :
    crossingFraction x j ∈ Icc (0 : ℝ) 1 := by
  have hvalid := x.2.2 j hj
  have hlt : historyHeight x j < historyHeight x (j + 1) := by
    by_cases hz : historyHeight x j = 0
    · exact hz ▸ x.2.1 j hz.ge
    · exact lt_of_lt_of_le (lt_of_le_of_ne hj.1 hz) hj.2
  have hclock := (Real.artanh_lt_artanh_iff hvalid.left_interior
    hvalid.right_interior).2 hlt
  have hA := Real.artanh_nonpos hj.1
  have hB := Real.artanh_nonneg hj.2
  dsimp [crossingFraction, historyHeight] at hA hB ⊢
  constructor
  · exact div_nonneg (neg_nonneg.mpr hA) (sub_pos.mpr hclock).le
  · apply (div_le_iff₀ (sub_pos.mpr hclock)).2
    linarith

def crossingPair {H : LocalEquiconnection K} (x : AdmissibleHistory H)
    (j : ℤ) (hj : Crossing (historyHeight x) j) : H.domain :=
  let hc := x.2.2 j hj
  ⟨(label ⟨x.1 j, hc.left_interior⟩, label ⟨x.1 (j + 1), hc.right_interior⟩), hc.labels⟩

/-- The formula uses the actual labels and arctanh heights of this history. -/
def chartValue {H : LocalEquiconnection K} (x : AdmissibleHistory H)
    (j : ℤ) (hj : Crossing (historyHeight x) j) : Suspension K :=
  phasePoint (H.connect (crossingPair x j hj, ⟨crossingFraction x j, crossingFraction_mem x j hj⟩))
    (-(j : ℝ) - crossingFraction x j)


end D5.S1.Dynamics.Shadowing.VerticalSuspensionSelector
