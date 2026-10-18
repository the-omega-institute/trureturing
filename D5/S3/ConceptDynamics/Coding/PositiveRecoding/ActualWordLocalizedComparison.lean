/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordLocalizedComparison
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordLocalizedComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The rectangular localized cochain equals the same actual positive-word gyration modulo three. -/
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.ActualPositiveWordPeriodicCochain
import D5.S3.ConceptDynamics.Coding.CountedLocalizedGyrationResidue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.ActualWordLocalizedComparison
open TwoSidedFiniteInduction TypedPositiveSplitWord ZeroWindowRelabeling
open CountedMatrixOverlap (CountMat)
open CountedOrderTypeGyration
open ActualPositiveWordPeriodicCochain
open SplitTowerTranslation
open CountedRelativeGyrationTransport

/-- The localized polynomial value at the literal nonnegative factors,
plus the actual finite-history chart corrections. Empty dimensions allowed. -/
def localizedCochain (d : ℕ) [NeZero d] (hd : 3 ∣ d) :
    ∀ {F H : Presentation}, Word F H → ZMod 3
  | _,_,.relabel r => ZMod.castHom hd (ZMod 3) ((relabelMap r).gyration d)
  | _,_,.positive R S old next =>
      -ZMod.castHom hd (ZMod 3) ((chartComparison old).gyration d) +
        dyadicGyration d
          ((R.map (Nat.castRingHom ℤ)).map (algebraMap ℤ GyrationDyadic))
          ((S.map (Nat.castRingHom ℤ)).map (algebraMap ℤ GyrationDyadic)) +
        ZMod.castHom hd (ZMod 3) ((chartComparison next).gyration d)
  | _,_,.comp u v => localizedCochain d hd u+localizedCochain d hd v

/-- Localized equality is proved at every actual positive leaf using the
supplier's nonnegative bridge, then composed along the actual endpoints. -/
theorem localizedCochain_eq : ∀ {F H : Presentation} (w : Word F H)
    (d : ℕ) [NeZero d] (hd : 3 ∣ d),
    localizedCochain d hd w = ZMod.castHom hd (ZMod 3) ((wordMap w).gyration d)
  | _,_,.relabel r,d,_,hd => rfl
  | _,_,.positive R S old next,d,_,hd => by
      rw [positive_gyration,map_add,map_add,map_neg]
      exact congrArg (fun z : ZMod 3 =>
        -ZMod.castHom hd (ZMod 3) ((chartComparison old).gyration d)+z+
          ZMod.castHom hd (ZMod 3) ((chartComparison next).gyration d))
        (dyadicGyration_nonnegative hd R S)
  | _,_,.comp u v,d,_,hd => by
      rw [wordMap_comp,TimedEquiv.gyration_comp,map_add]
      exact congrArg₂ (fun x y : ZMod 3 => x+y)
        (localizedCochain_eq u d hd) (localizedCochain_eq v d hd)

/-- Exact actual-history consequence. Nothing in this statement asserts that
the sum equals a one-edge cochain of rho(h); that is a different bridge. -/
theorem corrected_localized_word {F : Presentation} (w : Word F F) (s : ℤ)
    (h : Hist F ≃ Hist F)
    (ht : ∀ t x, h (time F.graph t x) = time F.graph t (h x))
    (hh : ∀ x, h x = time F.graph s (w.eval x))
    (d : ℕ) [NeZero d] (hd : 3 ∣ d) :
    ZMod.castHom hd (ZMod 3) (historyGyration h ht d) =
      localizedCochain d hd w+(Fintype.card (Orbit F d) : ZMod 3)*(s : ZMod 3) := by
  rw [time_corrected_word w s h ht hh d,map_add,map_mul,map_natCast,map_intCast,
    localizedCochain_eq,word_gyration]
end D5.S3.ConceptDynamics.Coding.ActualWordLocalizedComparison
