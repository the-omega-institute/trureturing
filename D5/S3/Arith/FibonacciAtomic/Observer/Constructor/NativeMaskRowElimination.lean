/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMaskRowElimination
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMaskRowElimination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native masks and reached sets recover complete original row exteriors. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicRowElimination

/-! Native mask restoration and complete row elimination on original prefix patterns. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeMaskRowElimination

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address)
open ActualCutPartitionRecovery (CutSet CutPrefixFree reachedHoles)
open ActualCutPartitionDecoder
  (HoleExterior cutExterior exteriorHoles actualPartition literalRecord)
open NativeGroundSeparation (Term evaluate)
open NativeSymbolicRecutting (SymbolicExterior exteriorFill symbolicExterior)
open NativeSymbolicRowElimination
open NativeTermUnification (Presentation)

/-- Replace precisely the encountered cut subtrees by the native leaf alpha. -/
def nativeMask (Q : CutSet) : Address → Source → Source
  | a, .of b => if a ∈ Q then .of true else .of b
  | a, .mul l r => if a ∈ Q then .of true else
      .mul (nativeMask Q (a ++ [false]) l) (nativeMask Q (a ++ [true]) r)

/-- Fill every literal address hole by alpha, retaining all concrete leaves. -/
def fillMask : HoleExterior →ₙ* Source :=
  FreeMagma.lift (Sum.elim FreeMagma.of (fun _ => .of true))

/-- The mask expression keeps every uncut frontier variable literally. -/
def maskExpression {X : Type} : SymbolicExterior X →ₙ* Term X :=
  FreeMagma.lift (Sum.elim FreeMagma.of (fun _ => .of (.inl true)))

private theorem mask_expression_fill {X : Type} (v : X → Source)
    (e : SymbolicExterior X) :
    evaluate v (maskExpression e) = fillMask (exteriorFill v e) := by
  have embedded : fillMask.comp (FreeMagma.map Sum.inl) = MulHom.id Source := by
    apply FreeMagma.hom_ext
    funext b
    rfl
  have h : (evaluate v).comp maskExpression = fillMask.comp (exteriorFill v) := by
    apply FreeMagma.hom_ext
    funext a
    cases a with
    | inl b => cases b with
      | inl b => rfl
      | inr x =>
          change v x = fillMask (FreeMagma.map Sum.inl (v x))
          exact (congrArg (fun f : Source →ₙ* Source => f (v x)) embedded).symm
    | inr q => rfl
  exact congrArg (fun f : SymbolicExterior X →ₙ* Source => f e) h

private theorem mask_fill (Q : CutSet) (a : Address) (u : Source) :
    nativeMask Q a u = fillMask (cutExterior Q a u) := by
  induction u generalizing a with
  | of b => by_cases h : a ∈ Q <;> simp [nativeMask, cutExterior, fillMask, h]
  | mul l r ihl ihr =>
      by_cases h : a ∈ Q
      · simp [nativeMask, cutExterior, fillMask, h]
      · simp only [nativeMask, cutExterior, h, ↓reduceIte, FreeMagma.mul_eq, map_mul]
        exact congrArg₂ (· * ·) (ihl _) (ihr _)

/-- Replacing the same cuts in the mask recovers every original exterior node. -/
private theorem mask_restore (Q : CutSet) (a : Address) (u : Source) :
    cutExterior Q a (nativeMask Q a u) = cutExterior Q a u := by
  induction u generalizing a with
  | of b => by_cases h : a ∈ Q <;> simp [nativeMask, cutExterior, h]
  | mul l r ihl ihr =>
      by_cases h : a ∈ Q
      · simp [nativeMask, cutExterior, h]
      · simp only [nativeMask, cutExterior, h, ↓reduceIte]
        exact congrArg₂ FreeMagma.mul (ihl _) (ihr _)

/-- Raw exteriors also have to put their literal address holes at their cuts.
This is a computed check, rather than an attained-label certificate. -/
private theorem mask_exterior_exact (Q : CutSet) (u : Source) (e : HoleExterior) :
    cutExterior Q [] u = e ↔
      cutExterior Q [] (fillMask e) = e ∧
      nativeMask Q [] u = fillMask e ∧
      (reachedHoles Q [] u).toFinset = (exteriorHoles [] e).toFinset := by
  constructor
  · intro h
    subst e
    refine ⟨?_, mask_fill Q [] u, ?_⟩
    · rw [← mask_fill, mask_restore]
    · rw [ActualCutPartitionDecoder.exteriorHoles_cut]
  · rintro ⟨coherent, mask, _⟩
    exact (mask_restore Q [] u).symm.trans
      ((congrArg (cutExterior Q []) mask).trans coherent)

private theorem mask_sources_exact (Q : CutSet) (u w : Source) :
    (nativeMask Q [] u = nativeMask Q [] w ∧
      (reachedHoles Q [] u).toFinset = (reachedHoles Q [] w).toFinset) ↔
      cutExterior Q [] u = cutExterior Q [] w := by
  rw [mask_exterior_exact]
  have coherent : cutExterior Q [] (fillMask (cutExterior Q [] w)) = cutExterior Q [] w := by
    rw [← mask_fill, mask_restore]
  rw [coherent, ← mask_fill, ActualCutPartitionDecoder.exteriorHoles_cut]
  simp only [true_and]

/-- Both complete exterior descriptors and the entire reached-pair relation.
The coherence conjunct rejects malformed raw address labels. -/
def maskRowHolds (r : RawRow) (u : Source) : Prop :=
  (cutExterior r.1 [] (fillMask r.2.1) = r.2.1 ∧
    nativeMask r.1 [] u = fillMask r.2.1 ∧
    (reachedHoles r.1 [] u).toFinset = (exteriorHoles [] r.2.1).toFinset) ∧
    actualPartition r.1 u = r.2.2

private theorem mask_row_exact (r : RawRow) (u : Source) :
    maskRowHolds r u ↔ literalRecord r.1 u = r.2 := by
  rcases r with ⟨Q, e, K⟩
  rw [maskRowHolds, ← mask_exterior_exact]
  simp only [literalRecord, Prod.mk.injEq]

/-- Mask and reached-set equality characterize complete original exteriors.
Every row of the same filled original pattern is then eliminated together,
with one unrestricted family reconstructing all original coordinates. -/
theorem original_mask_row_elimination {X : Type} (p : Presentation X)
    (d : Nat) (pat : NativeDepthPatterns.Pattern d)
    (name : NativeDepthPatterns.Frontier pat → X)
    (rs : List RawRow) (extra : SignedConstraints X) (v : X → Source)
    (freecuts : ∀ r ∈ rs, CutPrefixFree r.1)
    (bound : ∀ r ∈ rs, ∀ q ∈ r.1, q.length < d) :
    (∀ (Q : CutSet) (u w : Source),
      (nativeMask Q [] u = nativeMask Q [] w ∧
        (reachedHoles Q [] u).toFinset = (reachedHoles Q [] w).toFinset) ↔
        cutExterior Q [] u = cutExterior Q [] w) ∧
    (∀ r ∈ rs,
      evaluate v (maskExpression (symbolicExterior r.1 []
        (NativeHistoryCells.patternTerm pat name))) =
        nativeMask r.1 [] (NativeDepthPatterns.fill pat (v ∘ name))) ∧
    (((∀ r ∈ rs, maskRowHolds r (NativeDepthPatterns.fill pat (v ∘ name))) ∧
      constraintsHold extra v) ↔
      ∃ o, eliminateRows p (NativeHistoryCells.patternTerm pat name) rs extra = some o ∧
        outputHolds o v) := by
  refine ⟨mask_sources_exact, ?_, ?_⟩
  · intro r hr
    rw [mask_expression_fill]
    have deep := NativeHistoryCells.pattern_deep d d pat name [] (by simp)
    have he := (NativeSymbolicRecutting.symbolic_recut_exact d r.1
      (freecuts r hr) (bound r hr) (NativeHistoryCells.patternTerm pat name) deep v).2.1
    rw [← he, ← mask_fill, NativeHistoryCells.pattern_evaluate]
  · have rows :
        (∀ r ∈ rs, maskRowHolds r (NativeDepthPatterns.fill pat (v ∘ name))) ↔
        (∀ r ∈ rs, literalRecord r.1 (NativeDepthPatterns.fill pat (v ∘ name)) = r.2) := by
      constructor <;> intro h r hr
      · exact (mask_row_exact r _).mp (h r hr)
      · exact (mask_row_exact r _).mpr (h r hr)
    exact (and_congr rows Iff.rfl).trans
      ((complete_row_elimination p (NativeHistoryCells.patternTerm pat name) rs extra v).2
        d pat name rfl freecuts bound)

end D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeMaskRowElimination
