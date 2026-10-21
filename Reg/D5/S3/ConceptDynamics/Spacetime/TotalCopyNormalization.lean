import D5.S3.ConceptDynamics.Spacetime.TotalCopyNormalization
import Reg.Support.DependentFamily

/-! Source-family audit evidence for strict copy-tree interpretation. -/

set_option autoImplicit false
namespace Reg.D5.S3.ConceptDynamics.Spacetime.TotalCopyNormalization
open _root_.D5.S3.ConceptDynamics.Spacetime
open TotalCopyNormalization ComplementCharge
open _root_.D5.S3.ConceptDynamics.Observation.StrictOneHoleContexts
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev wordSignature : Signature where
  Params := List (Generator nativeSignature)
  State _ := B
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option B × Option B
  Anchor := Empty
  finiteAnchor := inferInstance

def wordActual : Realization wordSignature :=
  realize wordSignature (fun _ w X =>
    (evalDiagonal (wordToCopy w) X, contextDenote nativeSignature w X))
    (fun e => nomatch e)
def wordBad : Realization wordSignature :=
  realize wordSignature (fun _ _ _ => (none, some zero)) (fun e => nomatch e)
def wordArena : Arena where
  signature := wordSignature
  Law R := ∀ w X, (R.readout () w X).1 = (R.readout () w X).2

theorem wordBadFails : ¬ wordArena.Law wordBad := by
  intro h
  have h0 := h [] zero
  change (none : Option B) = some zero at h0
  cases h0

theorem sections_ne : ComplementFibers.balancedSection 3 0 ≠
    ComplementFibers.balancedSection 3 1 := by
  intro h
  have hh := congrArg ComplementFibers.balancedQ h
  have hh1 : (0 : Int) = 1 := by
    simpa only [ComplementFibers.balancedSection_readout] using hh
  omega

def wordRegistration : Registration wordArena
    (∀ w X, evalDiagonal (wordToCopy w) X = contextDenote nativeSignature w X) where
  actual := wordActual
  bridge := Iff.rfl
  variation := ⟨word_to_copy_denote, wordBad, wordBadFails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨wordBad, ?_, rfl, wordBadFails⟩
      intro j h
      change Unit at i j
      cases i
      cases j
      exact (h rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨[], ComplementFibers.balancedSection 3 0,
      ComplementFibers.balancedSection 3 1, ?_⟩
    intro h
    have hh : (some (ComplementFibers.balancedSection 3 0) : Option B) =
        some (ComplementFibers.balancedSection 3 1) := congrArg Prod.fst h
    exact sections_ne (Option.some.inj hh)

abbrev SubtreeParams := Σ n m : Nat, Binary × CopyTerm n × CopyTerm m
abbrev subtreeSignature : Signature where
  Params := SubtreeParams
  State _ := B
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option B × Option B × Option B × (B → B → Option B)
  Anchor := Empty
  finiteAnchor := inferInstance

def subtreeActual : Realization subtreeSignature :=
  realize subtreeSignature (fun _ p X =>
    (evalDiagonal (.binary p.2.2.1 p.2.2.2.1 p.2.2.2.2) X,
     evalDiagonal p.2.2.2.1 X, evalDiagonal p.2.2.2.2 X, binary p.2.2.1))
    (fun e => nomatch e)
def subtreeBad : Realization subtreeSignature :=
  realize subtreeSignature (fun _ _ _ =>
    (some zero, none, none, fun _ _ => none)) (fun e => nomatch e)
def subtreeArena : Arena where
  signature := subtreeSignature
  Law R := ∀ p X Y, (R.readout () p X).1 = some Y →
    ∃ x y, (R.readout () p X).2.1 = some x ∧
      (R.readout () p X).2.2.1 = some y ∧
      (R.readout () p X).2.2.2 x y = some Y

theorem subtreeBadFails : ¬ subtreeArena.Law subtreeBad := by
  intro h
  obtain ⟨x, y, hx, hy, hz⟩ := h ⟨1, 1, .parallel, .input, .input⟩ zero zero rfl
  change (none : Option B) = some x at hx
  cases hx

def subtreeRegistration : Registration subtreeArena
    (∀ {n m : Nat} (f : Binary) (a : CopyTerm n) (b : CopyTerm m) (X Y : B),
      evalDiagonal (.binary f a b) X = some Y →
      ∃ x y, evalDiagonal a X = some x ∧ evalDiagonal b X = some y ∧
        binary f x y = some Y) where
  actual := subtreeActual
  bridge := by
    constructor
    · intro h p X Y he
      exact h p.2.2.1 p.2.2.2.1 p.2.2.2.2 X Y he
    · intro h n m f a b X Y he
      exact h ⟨n, m, f, a, b⟩ X Y he
  variation := ⟨fun p X Y he => subtree_success _ _ _ X Y he, subtreeBad, subtreeBadFails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨subtreeBad, ?_, rfl, subtreeBadFails⟩
      intro j h
      change Unit at i j
      cases i
      cases j
      exact (h rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, 1, .parallel, .input, .input⟩,
      ComplementFibers.balancedSection 3 0, ComplementFibers.balancedSection 3 1, ?_⟩
    intro h
    have hh : (some (ComplementFibers.balancedSection 3 0) : Option B) =
        some (ComplementFibers.balancedSection 3 1) := congrArg (fun x => x.2.1) h
    exact sections_ne (Option.some.inj hh)

end
end Reg.D5.S3.ConceptDynamics.Spacetime.TotalCopyNormalization
