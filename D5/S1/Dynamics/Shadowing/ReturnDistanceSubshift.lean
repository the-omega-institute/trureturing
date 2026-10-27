/- GID: D5/S1/Dynamics/Shadowing/ReturnDistanceSubshift
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/ReturnDistanceSubshift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact binary return-distance subshifts and their exact-length word language. -/

import D5.S1.Dynamics.Shadowing.ReturnDistanceSupport
import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.UniformSpace.DiscreteUniformity

/-! Return distances count the step between successive ones; distance one is allowed
when one belongs to D. Finite supports and the zero configuration are included. -/

open Set Function SymbolicDynamics.FullShift
open scoped PiCountable

namespace D5.S1.Dynamics.Shadowing

/-- A binary finite alphabet with its inherited discrete metric. -/
abbrev ReturnBit := ↥(Finset.range 2)
def returnZero : ReturnBit := ⟨0, by decide⟩
def returnOne : ReturnBit := ⟨1, by decide⟩

@[simp] theorem return_zero_ne_one : returnZero ≠ returnOne := by decide

/-- The set of one coordinates of an actual two-sided configuration. -/
def oneSupport (x : ℤ → ReturnBit) : Set ℤ := {i | x i = returnOne}

def ReturnLegal (D : Set ℤ) (x : ℤ → ReturnBit) : Prop :=
  ∀ p q, SupportAdjacent (oneSupport x) p q → q - p ∈ D

/-- The local consecutive-pair condition is closed in the genuine product topology. -/
theorem return_legal_closed (D : Set ℤ) : IsClosed {x | ReturnLegal D x} := by
  have hopen (p q : ℤ) : IsOpen {x : ℤ → ReturnBit |
      SupportAdjacent (oneSupport x) p q} := by
    by_cases hpq : p < q
    · have he (i : ℤ) : IsOpen {x : ℤ → ReturnBit | x i = returnOne} := by
        simpa only [Set.preimage, Set.mem_singleton_iff] using
          (continuous_apply i : Continuous (fun x : ℤ → ReturnBit => x i)).isOpen_preimage
            ({returnOne} : Set ReturnBit) (isOpen_discrete _)
      have hn (i : ℤ) : IsOpen {x : ℤ → ReturnBit | x i ≠ returnOne} := by
        simpa only [Set.preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using
          (continuous_apply i : Continuous (fun x : ℤ → ReturnBit => x i)).isOpen_preimage
            ({returnOne}ᶜ : Set ReturnBit) (isOpen_discrete _)
      have hh := (Set.finite_Ioo p q).isOpen_biInter (fun i _ => hn i)
      convert (he p).inter ((he q).inter hh) using 1
      ext x
      simp [SupportAdjacent, oneSupport, hpq, and_assoc]
    · simp [SupportAdjacent, hpq]
  unfold ReturnLegal
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro p
  apply isClosed_iInter
  intro q
  apply isClosed_imp (hopen p q)
  by_cases hd : q - p ∈ D <;> simp [hd]

/-- All integer shifts preserve the same consecutive return distances. -/
theorem return_legal_shift {D : Set ℤ} {x : ℤ → ReturnBit}
    (hx : ReturnLegal D x) (g : ℤ) : ReturnLegal D (shift g x) := by
  intro p q hpq
  have hpqlt := hpq.2.2.1
  have hpair : SupportAdjacent (oneSupport x) (g + p) (g + q) := by
    refine ⟨hpq.1, hpq.2.1, by omega, ?_⟩
    intro t hpt htq ht
    apply hpq.2.2.2 (t - g) (by omega) (by omega)
    change x (g + (t - g)) = returnOne
    simpa [oneSupport] using ht
  have hd := hx (g + p) (g + q) hpair
  simpa using hd

/-- Bundled Mathlib subshift on a finite alphabet and integer coordinates. -/
def returnDistanceSubshift (D : Set ℤ) : SymbolicDynamics.FullShift.Subshift ReturnBit ℤ where
  carrier := {x | ReturnLegal D x}
  isClosed := return_legal_closed D
  mapsTo := fun g _ hx => return_legal_shift hx g

abbrev ReturnPoint (D : Set ℤ) := {x : ℤ → ReturnBit // ReturnLegal D x}

instance returnPointCompact (D : Set ℤ) : CompactSpace (ReturnPoint D) :=
  isCompact_iff_compactSpace.mp (return_legal_closed D).isCompact

/-- The actual shift by one on the subshift. -/
def returnShift (D : Set ℤ) (x : ReturnPoint D) : ReturnPoint D :=
  ⟨shift 1 x.1, return_legal_shift x.2 1⟩

theorem return_shift_continuous (D : Set ℤ) : Continuous (returnShift D) :=
  ((continuous_shift 1).comp continuous_subtype_val).subtype_mk _

/-- A support determines a binary configuration, with no finiteness assumption. -/
noncomputable def supportPoint (P : Set ℤ) : ℤ → ReturnBit := by
  classical
  exact fun i => if i ∈ P then returnOne else returnZero

@[simp] theorem one_support_point (P : Set ℤ) : oneSupport (supportPoint P) = P := by
  classical
  ext i
  simp [oneSupport, supportPoint]

/-- A configuration with at most one one is legal for every return-distance set. -/
theorem singleton_support_legal (D : Set ℤ) (s : ℤ) :
    ReturnLegal D (supportPoint {s}) := by
  intro p q hpq
  rw [one_support_point] at hpq
  have hp : p = s := hpq.1
  have hq : q = s := hpq.2.1
  have := hpq.2.2.1
  omega

/-- A finite word occurs in an actual subshift point at an integer coordinate. -/
def ReturnWordOccurs (w : List ReturnBit) (x : ℤ → ReturnBit) (t : ℤ) : Prop :=
  ∀ j : Fin w.length, x (t + (j : ℕ)) = w[j]

/-- The ordinary finite-word language of the bundled two-sided subshift. -/
def ReturnLanguage (D : Set ℤ) (w : List ReturnBit) : Prop :=
  ∃ x : ReturnPoint D, ∃ t : ℤ, ReturnWordOccurs w x.1 t

/-- Original exact-length quasi-finite type: the replacement has length exactly n. -/
def ReturnQuasiFiniteType (D : Set ℤ) : Prop :=
  ∃ M : ℕ, ∀ n : ℕ, M ≤ n → ∀ u v : List ReturnBit,
    ReturnLanguage D u → ReturnLanguage D v →
    (∃ w : List ReturnBit, w.length = n ∧ ReturnLanguage D w ∧
      ReturnLanguage D (u ++ w) ∧ ReturnLanguage D (w ++ v)) →
    ∃ z : List ReturnBit, z.length = n ∧ ReturnLanguage D z ∧
      ReturnLanguage D (u ++ z ++ v)

#print axioms return_legal_closed
#print axioms return_shift_continuous

end D5.S1.Dynamics.Shadowing
