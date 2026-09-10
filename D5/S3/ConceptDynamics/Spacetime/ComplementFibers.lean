/- GID: D5/S3/ConceptDynamics/Spacetime/ComplementFibers
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/ComplementFibers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/Spacetime/ComplementFibers.balanced_scalar_recovery_claim; result=D5/S3/ConceptDynamics/Spacetime/ComplementFibers.scalar_recovery_refuted; claim=D5/S3/ConceptDynamics/Spacetime/ComplementFibers.balanced_scalar_recovery_claim
   digest: Actual balanced archives occupy opposite readout fibers, while scalar sections forget event history. -/

import D5.S3.ConceptDynamics.Spacetime.IntegerRepresentatives
import D5.S3.ConceptDynamics.Spacetime.ComplementCharge
import D5.S3.ConceptDynamics.Negation.ComplementFiberLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Spacetime.ComplementFibers

open D5.S0.History.Spacetime
open ArchiveCarrier ComplementCharge
open D5.S3.ConceptDynamics.Spacetime.IntegerRepresentatives
open D5.S3.ConceptDynamics.Negation.ComplementFiberLift

noncomputable section
open scoped BigOperators

/- The generic B1 theorem is specialized here to the exact canonical
   representatives, retaining the distinction between event complement and
   numerical opposite fibers. -/
theorem representative_complement_mem_oppositeFiber (d : Nat) (n : Int) :
    complement (representative d n).2 ∈
      oppositeFiber (representative d n).2 := by
  exact balanced_complement_mem_oppositeFiber
    (representative_balanced d n) (representative d n).2

theorem empty_full_mem_oppositeFiber {d : Nat} (c : Context d)
    (h : Balanced c) :
    emptySelection c ∈ oppositeFiber (emptySelection c) ∧
      fullSelection c ∈ oppositeFiber (emptySelection c) := by
  constructor
  · change readout (emptySelection c) = -readout (emptySelection c)
    simp
  · change readout (fullSelection c) = -readout (emptySelection c)
    rw [show readout (fullSelection c) = background c by rfl, h]
    simp

theorem empty_full_distinct {d : Nat} {c : Context d}
    (hcurrent : c.current.Nonempty) :
    emptySelection c ≠ fullSelection c := by
  intro h
  have hs : (∅ : Finset c.Event) = c.current := congrArg Subtype.val h
  exact (Finset.nonempty_iff_ne_empty.mp hcurrent) hs.symm

theorem empty_full_fiber_members_distinct {d : Nat} (c : Context d)
    (h : Balanced c) (hcurrent : c.current.Nonempty) :
    emptySelection c ∈ oppositeFiber (emptySelection c) ∧
      fullSelection c ∈ oppositeFiber (emptySelection c) ∧
      emptySelection c ≠ fullSelection c := by
  exact ⟨(empty_full_mem_oppositeFiber c h).1,
    (empty_full_mem_oppositeFiber c h).2, empty_full_distinct hcurrent⟩

/- A section into the balanced rich-history carrier is fixed by the literal
   integer representatives from Definition 8. -/
def balancedRepresentative (d : Nat) (n : Int) : BalancedRich d :=
  ⟨representative d n, representative_balanced d n⟩

def balancedQ {d : Nat} (x : BalancedRich d) : Int := q x.val

def balancedSection (d : Nat) : Int → BalancedRich d := balancedRepresentative d

theorem balancedSection_readout (d : Nat) (n : Int) :
    balancedQ (balancedSection d n) = n := by
  exact representative_readout d n

theorem balancedSection_rightInverse (d : Nat) :
    Function.RightInverse (balancedSection d) (balancedQ : BalancedRich d → Int) := by
  intro n
  exact balancedSection_readout d n

/- All lift and recovery boundaries work in every dimension. The utility claim
   below fixes d=3, the source's actual spatial coordinate type. -/
def canonicalComplementLift (d : Nat) : BalancedRich d → BalancedRich d :=
  sectionLift balancedQ Neg.neg (balancedSection d)

theorem canonicalComplementLift_isComplementLift (d : Nat) :
  IsComplementLift balancedQ Neg.neg (canonicalComplementLift d) := by
  exact sectionLift_isComplementLift balancedQ Neg.neg (balancedSection d)
    (balancedSection_rightInverse d)

theorem canonicalComplementLift_square (d : Nat) :
  canonicalComplementLift d ∘ canonicalComplementLift d =
      balancedSection d ∘ balancedQ := by
  exact sectionLift_square balancedQ Neg.neg (balancedSection d)
    (balancedSection_rightInverse d) (by intro n; simp)

theorem canonicalComplementLift_involutive_iff_leftInverse (d : Nat) :
    Function.Involutive (canonicalComplementLift d) ↔
      Function.LeftInverse (balancedSection d) balancedQ := by
  exact sectionLift_involutive_iff_leftInverse balancedQ Neg.neg (balancedSection d)
    (balancedSection_rightInverse d) (by intro n; simp)

def emptyRich (d : Nat) (n : Int) : Rich d :=
  ⟨(representative d n).1, emptySelection (representative d n).1⟩

theorem emptyRich_balanced (d : Nat) (n : Int) : Balanced (emptyRich d n).1 := by
  exact representative_balanced d n

theorem emptyRich_readout (d : Nat) (n : Int) : q (emptyRich d n) = 0 := by
  simp [emptyRich, q, readout, emptySelection, charge]

theorem canonical_zero_readout (d : Nat) : q (representative d 0) = 0 :=
  representative_readout d 0

theorem canonical_one_empty_readout (d : Nat) : q (emptyRich d 1) = 0 :=
  emptyRich_readout d 1

theorem canonical_zero_ne_one_empty (d : Nat) :
    representative d 0 ≠ emptyRich d 1 := by
  intro h
  have hc := congrArg (fun x : Rich d => x.1.archive.events.card) h
  have hzero : (representative d 0).1.archive.events.card = 0 := by
    simpa [representative_archive_eq] using representative_archive_card d 0
  have hone : (emptyRich d 1).1.archive.events.card = 2 := by
    simpa [emptyRich, representative_archive_eq] using representative_archive_card d 1
  omega

theorem balanced_scalar_readout_not_injective (d : Nat) :
    ¬ Function.Injective (balancedQ : BalancedRich d → Int) := by
  intro hinj
  have heq : balancedQ (balancedRepresentative d 0) =
      balancedQ ⟨emptyRich d 1, emptyRich_balanced d 1⟩ := by
    change q (representative d 0) = q (emptyRich d 1)
    rw [canonical_zero_readout, canonical_one_empty_readout]
  have hhist : balancedRepresentative d 0 =
      (⟨emptyRich d 1, emptyRich_balanced d 1⟩ : BalancedRich d) := hinj heq
  exact canonical_zero_ne_one_empty d (congrArg Subtype.val hhist)

theorem scalar_readout_not_injective (d : Nat) :
    ¬ Function.Injective (q : Rich d → Int) := by
  intro hinj
  apply balanced_scalar_readout_not_injective d
  intro x y hxy
  exact Subtype.ext (hinj hxy)

def balanced_scalar_recovery_claim : Prop :=
  ∃ s : Int → BalancedRich 3,
    Function.LeftInverse s (balancedQ : BalancedRich 3 → Int)

theorem scalar_recovery_refuted : ¬ balanced_scalar_recovery_claim := by
  rintro ⟨s, hs⟩
  exact balanced_scalar_readout_not_injective 3 hs.injective

theorem canonical_section_not_leftInverse (d : Nat) :
    ¬ Function.LeftInverse (balancedSection d)
      (balancedQ : BalancedRich d → Int) := by
  intro h
  exact balanced_scalar_readout_not_injective d h.injective

theorem canonicalComplementLift_not_involutive (d : Nat) :
    ¬ Function.Involutive (canonicalComplementLift d) := by
  intro h
  exact canonical_section_not_leftInverse d
    ((canonicalComplementLift_involutive_iff_leftInverse d).mp h)

theorem sectionLift_square_readout {d : Nat} (s : Int → BalancedRich d)
    (hs : Function.RightInverse s (balancedQ : BalancedRich d → Int)) :
    sectionLift balancedQ Neg.neg s ∘ sectionLift balancedQ Neg.neg s =
      s ∘ balancedQ := by
  exact sectionLift_square balancedQ Neg.neg s hs (by intro n; simp)

end
end D5.S3.ConceptDynamics.Spacetime.ComplementFibers
