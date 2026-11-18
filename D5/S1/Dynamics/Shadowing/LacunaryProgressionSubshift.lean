/- GID: D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/LacunaryProgressionSubshift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact two-sided binary subshifts excluding triples on lacunary progressions. -/

import D5.S1.Dynamics.Shadowing.ReturnDistanceShadowing

/-! The constraint forbids three occupied vertices in every prescribed
progression; the state space carries the inherited product metric. -/

open Set Function SymbolicDynamics.FullShift
open scoped PiCountable

namespace D5.S1.Dynamics.Shadowing

/-- A single nonempty finite tracer set, with its initial diameter controlled. -/
def NeighborhoodFiniteShadowing (N : ℕ) {X : Type*} [MetricSpace X]
    (f : X → X) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ z : ℕ → X, MetricPseudoOrbit f δ z →
    ∃ A : Finset X, A.Nonempty ∧ A.card ≤ N ∧ Metric.diam (A : Set X) < ε ∧
      ∀ i, Metric.infDist (z i) (f^[i] '' (A : Set X)) < ε

/-- No three distinct places in any prescribed lacunary progression are ones. -/
def LacunaryLegal (m : ℕ) (x : ℤ → ReturnBit) : Prop :=
  ∀ (s : ℤ) (k : ℕ) (i j l : Fin m), i ≠ j → i ≠ l → j ≠ l →
    ¬ (x (s + (i.val : ℤ) * ((m + 1 : ℕ) : ℤ)^k) = returnOne ∧
      x (s + (j.val : ℤ) * ((m + 1 : ℕ) : ℤ)^k) = returnOne ∧
      x (s + (l.val : ℤ) * ((m + 1 : ℕ) : ℤ)^k) = returnOne)

abbrev LacunaryPoint (m : ℕ) := {x : ℤ → ReturnBit // LacunaryLegal m x}

/-- The legal configurations are an intersection of closed complements of cylinders. -/
theorem lacunary_legal_closed (m : ℕ) : IsClosed {x | LacunaryLegal m x} := by
  unfold LacunaryLegal
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun s => isClosed_iInter fun k =>
    isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun l =>
    isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
  have he (t : ℤ) : IsClopen {x : ℤ → ReturnBit | x t = returnOne} :=
    (isClopen_discrete ({returnOne} : Set ReturnBit)).preimage (continuous_apply t)
  exact ((he _).inter ((he _).inter (he _))).isOpen.isClosed_compl

/-- Every integer translation preserves the progression constraints. -/
theorem lacunary_legal_shift {m : ℕ} {x : ℤ → ReturnBit}
    (hx : LacunaryLegal m x) (g : ℤ) : LacunaryLegal m (shift g x) := by
  intro s k i j l hij hil hjl
  simpa only [shift_apply, add_assoc] using hx (g + s) k i j l hij hil hjl

/-- The genuine Mathlib full-shift subshift, with integer coordinates. -/
def lacunarySubshift (m : ℕ) : SymbolicDynamics.FullShift.Subshift ReturnBit ℤ where
  carrier := {x | LacunaryLegal m x}
  isClosed := lacunary_legal_closed m
  mapsTo := fun g _ hx => lacunary_legal_shift hx g

instance lacunaryPointCompact (m : ℕ) : CompactSpace (LacunaryPoint m) :=
  isCompact_iff_compactSpace.mp (lacunary_legal_closed m).isCompact

/-- Supports of cardinality at most one cannot contain a forbidden triple. -/
theorem lacunary_legal_of_subsingleton_support {m : ℕ} {x : ℤ → ReturnBit}
    (hx : (oneSupport x).Subsingleton) : LacunaryLegal m x := by
  intro s k i j l hij _ _ hones
  have he := hx hones.1 hones.2.1
  have hpos : (0 : ℤ) < ((m + 1 : ℕ) : ℤ)^k := pow_pos (by omega) k
  have hmul : (i.val : ℤ) * ((m + 1 : ℕ) : ℤ)^k =
      (j.val : ℤ) * ((m + 1 : ℕ) : ℤ)^k := add_left_cancel he
  have hv : (i.val : ℤ) = (j.val : ℤ) :=
    mul_right_cancel₀ (ne_of_gt hpos) hmul
  exact hij (Fin.ext (by exact_mod_cast hv))

theorem lacunary_zero_legal (m : ℕ) : LacunaryLegal m (fun _ => returnZero) := by
  intro s k i j l _ _ _ h
  exact return_zero_ne_one h.1

instance lacunaryPointNonempty (m : ℕ) : Nonempty (LacunaryPoint m) :=
  ⟨⟨fun _ => returnZero, lacunary_zero_legal m⟩⟩

/-- The restriction of the actual integer shift by one. -/
def lacunaryShift (m : ℕ) (x : LacunaryPoint m) : LacunaryPoint m :=
  ⟨shift 1 x.1, lacunary_legal_shift x.2 1⟩

theorem lacunary_shift_continuous (m : ℕ) : Continuous (lacunaryShift m) :=
  ((continuous_shift 1).comp continuous_subtype_val).subtype_mk _

/-- Natural-time iteration reads the corresponding genuine integer coordinate. -/
theorem lacunary_shift_iterate (m : ℕ) (x : LacunaryPoint m) (i : ℕ) (j : ℤ) :
    ((lacunaryShift m)^[i] x).1 j = x.1 ((i : ℤ) + j) := by
  induction i generalizing x j with
  | zero => simp
  | succ i ih =>
    rw [iterate_succ_apply, ih]
    change x.1 (1 + ((i : ℤ) + j)) = x.1 ((↑(i + 1) : ℤ) + j)
    have he : 1 + ((i : ℤ) + j) = ((i + 1 : ℕ) : ℤ) + j := by omega
    rw [he]

end D5.S1.Dynamics.Shadowing
