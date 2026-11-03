/- GID: D5/S1/Dynamics/Shadowing/ProgressionSubshift
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/ProgressionSubshift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One-sided hereditary progression subshifts and exclusion of nonempty periodic sets. -/

import D5.S1.Dynamics.Shadowing.ReturnDistanceShadowing

/-! Progression constraints use positive differences and include every starting
coordinate. The configuration metric is the first-disagreement metric. -/

open Set Function SymbolicDynamics.FullShift

namespace D5.S1.Dynamics.Shadowing

/-- The genuine first-disagreement metric on the one-sided binary product. -/
noncomputable instance progressionConfigurationMetric : MetricSpace (ℕ → ReturnBit) :=
  PiNat.metricSpaceOfDiscreteUniformity fun _ => DiscreteUniformity.eq_principal_setRelId _

/-- Every positive-step progression of the prescribed length contains a zero. -/
def ProgressionLegal (ℓ : ℕ → ℕ) (x : ℕ → ReturnBit) : Prop :=
  ∀ s p : ℕ, 0 < p → ∃ j < ℓ p, x (s + j * p) = returnZero

theorem progression_legal_closed (ℓ : ℕ → ℕ) :
    IsClosed {x | ProgressionLegal ℓ x} := by
  unfold ProgressionLegal
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun s => isClosed_iInter fun p => isClosed_iInter fun _ => ?_
  have he (j : ℕ) : IsClosed {x : ℕ → ReturnBit | x (s + j * p) = returnZero} :=
    isClosed_singleton.preimage (continuous_apply _)
  convert (Set.finite_Iio (ℓ p)).isClosed_biUnion (fun j _ => he j) using 1
  ext x
  simp

theorem progression_legal_shift {ℓ : ℕ → ℕ} {x : ℕ → ReturnBit}
    (hx : ProgressionLegal ℓ x) (n : ℕ) : ProgressionLegal ℓ (shift n x) := by
  intro s p hp
  obtain ⟨j, hj, hz⟩ := hx (n + s) p hp
  exact ⟨j, hj, by simpa [shift_apply, Nat.add_assoc] using hz⟩

abbrev ProgressionPoint (ℓ : ℕ → ℕ) := {x : ℕ → ReturnBit // ProgressionLegal ℓ x}

instance progressionPointCompact (ℓ : ℕ → ℕ) : CompactSpace (ProgressionPoint ℓ) :=
  isCompact_iff_compactSpace.mp (progression_legal_closed ℓ).isCompact

def progressionShift (ℓ : ℕ → ℕ) (x : ProgressionPoint ℓ) : ProgressionPoint ℓ :=
  ⟨shift 1 x.1, progression_legal_shift x.2 1⟩

theorem progression_shift_continuous (ℓ : ℕ → ℕ) : Continuous (progressionShift ℓ) :=
  ((continuous_shift 1).comp continuous_subtype_val).subtype_mk _

theorem progression_shift_iterate (ℓ : ℕ → ℕ) (x : ProgressionPoint ℓ) (i j : ℕ) :
    ((progressionShift ℓ)^[i] x).1 j = x.1 (i + j) := by
  have h : ((progressionShift ℓ)^[i] x).1 = (shift (1 : ℕ))^[i] x.1 := by
    induction i with
    | zero => rfl
    | succ i ih => simp only [iterate_succ_apply', progressionShift, ih]
  rw [h, shift_one_iterate_apply]

theorem progression_zero_legal {ℓ : ℕ → ℕ} (hℓ : ∀ p, 0 < p → 0 < ℓ p) :
    ProgressionLegal ℓ (fun _ => returnZero) := by
  intro s p hp
  exact ⟨0, hℓ p hp, rfl⟩

theorem progression_prepend_zero_legal {ℓ : ℕ → ℕ}
    (hℓ : ∀ p, 0 < p → 0 < ℓ p) {x : ℕ → ReturnBit} (hx : ProgressionLegal ℓ x) :
    ProgressionLegal ℓ (fun k => if k = 0 then returnZero else x (k - 1)) := by
  intro s p hp
  rcases s with _ | s
  · exact ⟨0, hℓ p hp, by simp⟩
  · obtain ⟨j, hj, hz⟩ := hx s p hp
    refine ⟨j, hj, ?_⟩
    change (if s + 1 + j * p = 0 then _ else _) = _
    rw [ite_eq_right (by omega)]
    convert hz using 1
    congr 1
    omega

theorem progression_shift_surjective {ℓ : ℕ → ℕ}
    (hℓ : ∀ p, 0 < p → 0 < ℓ p) : Surjective (progressionShift ℓ) := by
  intro x
  refine ⟨⟨_, progression_prepend_zero_legal hℓ x.2⟩, ?_⟩
  apply Subtype.ext
  funext k
  simp [progressionShift, shift_apply, Nat.add_comm]

theorem progression_singleton_legal {ℓ : ℕ → ℕ}
    (hℓ : ∀ p, 0 < p → 2 ≤ ℓ p) :
    ProgressionLegal ℓ (fun k => if k = 0 then returnOne else returnZero) := by
  intro s p hp
  refine ⟨1, by have := hℓ p hp; omega, ?_⟩
  simp only [one_mul, ite_eq_right_iff]
  intro h
  omega

def progressionOneCylinder (ℓ : ℕ → ℕ) : Set (ProgressionPoint ℓ) :=
  {x | x.1 0 = returnOne}

theorem progression_one_cylinder_clopen (ℓ : ℕ → ℕ) :
    IsClopen (progressionOneCylinder ℓ) := by
  exact (isClopen_discrete ({returnOne} : Set ReturnBit)).preimage
    ((continuous_apply 0).comp continuous_subtype_val)

theorem progression_one_cylinder_nonempty {ℓ : ℕ → ℕ}
    (hℓ : ∀ p, 0 < p → 2 ≤ ℓ p) : (progressionOneCylinder ℓ).Nonempty :=
  ⟨⟨_, progression_singleton_legal hℓ⟩, rfl⟩

/-- No nonempty subset of the one cylinder is even forward invariant under a
positive power. Compactness and equality of the image are unnecessary. -/
theorem progression_no_invariant_subset (ℓ : ℕ → ℕ) (p : ℕ) (hp : 0 < p)
    (B : Set (ProgressionPoint ℓ)) (hB : B ⊆ progressionOneCylinder ℓ)
    (hinv : MapsTo ((progressionShift ℓ)^[p]) B B) : ¬ B.Nonempty := by
  rintro ⟨x, hx⟩
  have horbit (j : ℕ) : (progressionShift ℓ)^[j * p] x ∈ B := by
    induction j with
    | zero => simpa using hx
    | succ j ih =>
      simpa only [Nat.succ_mul, Nat.add_comm (j * p) p, iterate_add_apply] using hinv ih
  obtain ⟨j, _, hz⟩ := x.2 0 p hp
  have ho := hB (horbit j)
  change (((progressionShift ℓ)^[j * p] x).1 0) = returnOne at ho
  rw [progression_shift_iterate] at ho
  simp only [Nat.add_zero, Nat.zero_add] at ho hz
  exact return_zero_ne_one (hz.symm.trans ho)

/-- Two allowed prefixes separated by a sufficiently long zero gap. -/
def progressionJoin (x y : ℕ → ReturnBit) (a b n : ℕ) : ℕ → ReturnBit :=
  fun k => if k < a then x k else if n ≤ k ∧ k < n + b then y (k - n) else returnZero

/-- The zero gap prevents a new forbidden progression from joining the words.
The length assumption is only three, independently of its growth. -/
theorem progression_join_legal {ℓ : ℕ → ℕ} (hℓ : ∀ p, 0 < p → 3 ≤ ℓ p)
    {x y : ℕ → ReturnBit} (hx : ProgressionLegal ℓ x) (hy : ProgressionLegal ℓ y)
    (a b n : ℕ) (hn : a + max a b ≤ n) :
    ProgressionLegal ℓ (progressionJoin x y a b n) := by
  classical
  intro s p hp
  by_contra! hbad
  have hsupport (j : ℕ) (hj : j < ℓ p) :
      s + j * p < a ∨ (n ≤ s + j * p ∧ s + j * p < n + b) := by
    have hz := hbad j hj
    by_contra! hout
    exact hz (by simp [progressionJoin, show ¬s + j * p < a by omega,
      show ¬(n ≤ s + j * p ∧ s + j * p < n + b) by omega])
  have hlen := hℓ p hp
  have h0 := hsupport 0 (by omega)
  simp only [Nat.zero_mul, Nat.add_zero] at h0
  have ha : a ≤ n := by omega
  have hmaxa := le_max_left a b
  have hmaxb := le_max_right a b
  rcases h0 with hsa | hsn
  · by_cases hsmall : p ≤ max a b
    · have hall (j : ℕ) (hj : j < ℓ p) : s + j * p < a := by
        induction j with
        | zero => simpa using hsa
        | succ j ih =>
          have hprev := ih (by omega)
          rcases hsupport (j + 1) hj with ht | ht
          · exact ht
          · have : s + (j + 1) * p = s + j * p + p := by ring
            omega
      obtain ⟨j, hj, hz⟩ := hx s p hp
      exact hbad j hj (by simp [progressionJoin, hall j hj, hz])
    · have hpbig : max a b < p := by omega
      have h1 := hsupport 1 (by omega)
      have h2 := hsupport 2 (by omega)
      simp only [one_mul] at h1
      have hh : s + 2 * p = (s + p) + p := by omega
      omega
  · obtain ⟨j, hj, hz⟩ := hy (s - n) p hp
    have hsj : n ≤ s + j * p := by omega
    have hsja : ¬ s + j * p < a := by omega
    have hupper := (hsupport j hj).resolve_left hsja
    have heq : s + j * p - n = s - n + j * p := by omega
    exact hbad j hj (by simp [progressionJoin, hsja, hupper, heq, hz])

/-- Open-set mixing, with every sufficiently large natural hitting time. -/
theorem progression_shift_mixing {ℓ : ℕ → ℕ} (hℓ : ∀ p, 0 < p → 3 ≤ ℓ p)
    (U V : Set (ProgressionPoint ℓ)) (hU : IsOpen U) (hV : IsOpen V)
    (hUn : U.Nonempty) (hVn : V.Nonempty) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z ∈ U, (progressionShift ℓ)^[n] z ∈ V := by
  obtain ⟨x, hx⟩ := hUn
  obtain ⟨y, hy⟩ := hVn
  obtain ⟨ε, hε, hxball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨η, hη, hyball⟩ := Metric.isOpen_iff.mp hV y hy
  obtain ⟨a, ha⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨b, hb⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨a + max a b, fun n hn => ?_⟩
  let z : ProgressionPoint ℓ :=
    ⟨progressionJoin x.1 y.1 a b n, progression_join_legal hℓ x.2 y.2 a b n hn⟩
  refine ⟨z, hxball ?_, hyball ?_⟩
  · apply lt_of_le_of_lt _ ha
    change dist z.1 x.1 ≤ _
    apply PiNat.mem_cylinder_iff_dist_le.mp
    intro k hk
    simp [z, progressionJoin, hk]
  · apply lt_of_le_of_lt _ hb
    change dist (((progressionShift ℓ)^[n] z).1) y.1 ≤ _
    apply PiNat.mem_cylinder_iff_dist_le.mp
    intro k hk
    rw [progression_shift_iterate]
    have hna : a ≤ n := by omega
    simp [z, progressionJoin, show ¬n + k < a by omega, show n ≤ n + k by omega,
      show n + k < n + b by omega]

end D5.S1.Dynamics.Shadowing
