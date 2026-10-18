import D5.S3.ConceptDynamics.Coding.PositiveRecoding.PresentationTimeCochain
import D5.S3.ConceptDynamics.Coding.OriginalRoot.CentralizerTimePowers
import D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.SetTheory.Cardinal.Finite
import D5.S3.ConceptDynamics.Coding.TwistedPeriodicHistories
import D5.S3.ConceptDynamics.Coding.CountedSignedGyrationEvaluator
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.ActualWordEnumeratedLoop
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.OriginalPositiveWordAssembly
import D5.S3.ConceptDynamics.Coding.ResponseRealization.OriginalResponseTableIntake
import D5.S3.ConceptDynamics.Coding.BeamColimits.PositiveWordFullAction
import D5.S3.ConceptDynamics.Coding.OriginalRoot.ResetQ4LocalizedGyrationCharacter

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding
open EssentialWordRealization FiniteWindowTableCriterion
open TwoSidedFiniteInduction TypedPositiveSplitWord
open StandardBeamCoordinates StandardBeamColimitCuts StandardBeamHomeomorphisms
open StandardTaggedBeams StandardBeamIdentification ResetNumberedHistories
open ResetStandardBeamGeometry ResetFullStandardBeamRepresentation
open OriginalResponseTableIntake ResponseTwoSidedConsumer OriginalPositiveWordAssembly
open ResetNativeIntegralDefect
open ActualPositiveWordPeriodicCochain ActualWordLocalizedComparison
open CountedOrderTypeGyration (dyadicGyration integerGyrationValue rotate)
open CountedOrderTypeGyration.SignedSupport
  (prunedShard integerGyrationValue_eq_supportedEvaluator
    supportedEvaluator_eq_pruned prunedEvaluator_eq_shards keyWeight sourceKeys targetKeys
    middleWords rankVectors vectorTerm SkeletonMinimal rankWidth coefficient
    vectorTerm_zero_of_nonminimal sSlots KeyLT skeleton Key KeyWordLT KeyLeast)
open ResetQ4OriginalLocalizedCubes (T VertexIndex DyadicMatrix)
open ResetQ4LocalizedGyrationCharacter
  (originalRows vertexEquiv originalRows_mul originalRows_one columnGyration
    columnGyration_triangle gamma Gamma originalAdjacency onePlusSignedFactor
    gamma_time_signed_evaluation gamma_onePlus_signed_evaluation)
open TwistedPeriodicHistories FixedBlockRigidity
open CountedOrderTypeGyration (primitivePath_card_eq_period_mul_orbit_card)
open SourceOnly.ActualWordMatrixPath (D vertex presentationBasis endpointMap timeMap)
open SourceOnly.ActualWordEnumeratedLoop
open SourceOnly.BasedLoopCoordinateTransport
open SourceOnly.KernelRSSquareGyration (rows value)
open SourceOnly.FiniteKernelLadder (Mat rowUnit)
open scoped BigOperators Matrix

local instance nativeIntModule (q : ℕ) :
    Module ℤ (InertGroupBlockConjugacy.DimensionGroup (resetMatrix q)) :=
  AddCommGroup.toIntModule _

def zeroRanks {d : ℕ} : Fin d → ℕ := fun _ => 0

def nextWord {d : ℕ} [NeZero d] (a : Fin d → Fin 8) : Fin d → Fin 8 :=
  fun t => a (t + 1)

def validAdj {d : ℕ} [NeZero d] (R : Matrix (Fin 8) (Fin 8) ℤ) (a : Fin d → Fin 8) : Prop :=
  ∀ t, R (a t) (a (t + 1)) ≠ 0

def validAdj6 (R : Matrix (Fin 8) (Fin 8) ℤ) (a : Fin 6 → Fin 8) : Prop :=
  R (a 0) (a 1) ≠ 0 ∧ R (a 1) (a 2) ≠ 0 ∧ R (a 2) (a 3) ≠ 0 ∧
  R (a 3) (a 4) ≠ 0 ∧ R (a 4) (a 5) ≠ 0 ∧ R (a 5) (a 0) ≠ 0

instance validAdj6_decidable (R : Matrix (Fin 8) (Fin 8) ℤ) (a : Fin 6 → Fin 8) :
    Decidable (validAdj6 R a) := by
  unfold validAdj6
  infer_instance

theorem validAdj6_iff (R : Matrix (Fin 8) (Fin 8) ℤ) (a : Fin 6 → Fin 8) :
    validAdj6 R a ↔ ∀ t, R (a t) (a (t + 1)) ≠ 0 := by
  constructor
  · intro h t
    rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
    fin_cases t
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
    · simpa using h4
    · simpa using h5
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩

def fastTimeShard (i : Fin 8) : ℤ :=
  ∑ tail : Fin 5 → Fin 8,
    let a : Fin 6 → Fin 8 := Fin.cons i tail
    if h : validAdj6 originalAdjacency a then
      keyWeight (sourceKeys (a, nextWord a) zeroRanks)
        (targetKeys (a, nextWord a) zeroRanks)
    else 0

theorem sumConsFin8 {k : ℕ} (f : (Fin (k+1) → Fin 8) → ℤ) :
    (∑ a, f a) = ∑ i : Fin 8, ∑ tail : Fin k → Fin 8, f (Fin.cons i tail) := by
  exact ((Fin.consEquiv (fun _ : Fin (k+1) => Fin 8)).sum_comp f).symm.trans
    (Fintype.sum_prod_type _)

def onePlusMiddleFiber (x y : Fin 8) : Finset (Fin 8) :=
  ![
    ![(∅ : Finset (Fin 8)), {2}, {0}, {1, 2}, {0, 2}, {1, 2}, {0, 2}, {1, 2}],
    ![{3}, ∅, {0, 3}, {1}, {0, 3}, {1, 3}, {0, 3}, {1, 3}],
    ![∅, {2}, ∅, {1, 2}, {2}, {1, 2}, {2, 4}, {1, 2}],
    ![{3}, ∅, {0, 3}, ∅, {0, 3}, {3}, {0, 3}, {3, 5}],
    ![∅, {6}, ∅, {1, 6}, ∅, {1, 6}, {4}, {1, 6}],
    ![{7}, ∅, {0, 7}, ∅, {0, 7}, ∅, {0, 7}, {5}],
    ![∅, {6}, ∅, {1, 6}, ∅, {1, 6}, ∅, {1, 6}],
    ![{7}, ∅, {0, 7}, ∅, {0, 7}, ∅, {0, 7}, ∅]
  ] x y

def onePlusMiddleWords (a : Fin 6 → Fin 8) : Finset (Fin 6 → Fin 8) :=
  Fintype.piFinset fun t : Fin 6 => onePlusMiddleFiber (a t) (a (t + 1))

theorem onePlusMiddleFiber_eq (x y : Fin 8) :
    onePlusMiddleFiber x y =
      Finset.univ.filter (fun j : Fin 8 =>
        (1 + originalAdjacency) x j ≠ 0 ∧ onePlusSignedFactor j y ≠ 0) := by
  fin_cases x <;> fin_cases y <;> decide +kernel

theorem onePlusMiddleWords_eq (a : Fin 6 → Fin 8) :
    onePlusMiddleWords a = middleWords (1 + originalAdjacency) onePlusSignedFactor a := by
  classical
  ext b
  simp only [onePlusMiddleWords, middleWords, Fintype.mem_piFinset]
  constructor
  · intro h t
    have ht := h t
    rw [onePlusMiddleFiber_eq] at ht
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ht
  · intro h t
    have ht : b t ∈ Finset.univ.filter (fun j : Fin 8 =>
        (1 + originalAdjacency) (a t) j ≠ 0 ∧ onePlusSignedFactor j (a (t + 1)) ≠ 0) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h t)⟩
    rw [← onePlusMiddleFiber_eq] at ht
    exact ht


def sourcePairLT (a : Fin 6 → Fin 8) (t : Fin 6) : Prop :=
  (a t).val < (a 0).val ∨
    ((a t).val = (a 0).val ∧ (a (t + 1)).val < (a 1).val)

instance sourcePairLT_decidable (a : Fin 6 → Fin 8) (t : Fin 6) :
    Decidable (sourcePairLT a t) := by
  unfold sourcePairLT
  infer_instance

def sourceMinimal (a : Fin 6 → Fin 8) : Prop :=
  ∀ t, ¬ sourcePairLT a t

instance sourceMinimal_decidable (a : Fin 6 → Fin 8) :
    Decidable (sourceMinimal a) := by
  unfold sourceMinimal
  infer_instance

def sourceMinimal6Fast (a : Fin 6 → Fin 8) : Prop :=
  ¬ sourcePairLT a 0 ∧ ¬ sourcePairLT a 1 ∧ ¬ sourcePairLT a 2 ∧
    ¬ sourcePairLT a 3 ∧ ¬ sourcePairLT a 4 ∧ ¬ sourcePairLT a 5

instance sourceMinimal6Fast_decidable (a : Fin 6 → Fin 8) :
    Decidable (sourceMinimal6Fast a) := by
  unfold sourceMinimal6Fast
  infer_instance

theorem sourceMinimal6Fast_iff (a : Fin 6 → Fin 8) :
    sourceMinimal6Fast a ↔ sourceMinimal a := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ t
    fin_cases t <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩

theorem sourcePairLT_skeleton {a : Fin 6 → Fin 8} {b : Fin 6 → Fin 8}
    {t : Fin 6} (h : sourcePairLT a t) :
    KeyLT (skeleton (a,b) t) (skeleton (a,b) 0) := by
  rcases h with h | ⟨h0, h1⟩
  · exact Or.inl h
  · exact Or.inr ⟨h0, Or.inl h1⟩

def pathValid (a : Fin 6 → Fin 8) : Prop :=
  ∀ t, (onePlusMiddleFiber (a t) (a (t + 1))).Nonempty

instance pathValid_decidable (a : Fin 6 → Fin 8) : Decidable (pathValid a) := by
  unfold pathValid
  infer_instance

def pathValid6Fast (a : Fin 6 → Fin 8) : Prop :=
  (onePlusMiddleFiber (a 0) (a (0 + 1))).Nonempty ∧
  (onePlusMiddleFiber (a 1) (a (1 + 1))).Nonempty ∧
  (onePlusMiddleFiber (a 2) (a (2 + 1))).Nonempty ∧
  (onePlusMiddleFiber (a 3) (a (3 + 1))).Nonempty ∧
  (onePlusMiddleFiber (a 4) (a (4 + 1))).Nonempty ∧
  (onePlusMiddleFiber (a 5) (a (5 + 1))).Nonempty

instance pathValid6Fast_decidable (a : Fin 6 → Fin 8) :
    Decidable (pathValid6Fast a) := by
  unfold pathValid6Fast
  infer_instance

theorem pathValid6Fast_iff (a : Fin 6 → Fin 8) :
    pathValid6Fast a ↔ pathValid a := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ t
    fin_cases t <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩

def skeletonMinimal6Fast
    (w : CountedOrderTypeGyration.VertexWord 8 8 6) : Prop :=
  ¬ KeyLT (skeleton w 1) (skeleton w 0) ∧
  ¬ KeyLT (skeleton w 2) (skeleton w 0) ∧
  ¬ KeyLT (skeleton w 3) (skeleton w 0) ∧
  ¬ KeyLT (skeleton w 4) (skeleton w 0) ∧
  ¬ KeyLT (skeleton w 5) (skeleton w 0)

instance skeletonMinimal6Fast_decidable
    (w : CountedOrderTypeGyration.VertexWord 8 8 6) :
    Decidable (skeletonMinimal6Fast w) := by
  unfold skeletonMinimal6Fast
  infer_instance

theorem skeletonMinimal6Fast_iff
    (w : CountedOrderTypeGyration.VertexWord 8 8 6) :
    skeletonMinimal6Fast w ↔ SkeletonMinimal w := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩ t
    fin_cases t
    · simp [KeyLT]
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro h
    exact ⟨h 1, h 2, h 3, h 4, h 5⟩


def slotSet6 (w : Fin 6 → Fin 8 × Fin 8) (e : Fin 8 × Fin 8) : Finset (Fin 6) :=
  (if (w 0) = e then ({0} : Finset (Fin 6)) else ∅) ∪
  (if (w 1) = e then ({1} : Finset (Fin 6)) else ∅) ∪
  (if (w 2) = e then ({2} : Finset (Fin 6)) else ∅) ∪
  (if (w 3) = e then ({3} : Finset (Fin 6)) else ∅) ∪
  (if (w 4) = e then ({4} : Finset (Fin 6)) else ∅) ∪
  (if (w 5) = e then ({5} : Finset (Fin 6)) else ∅)

theorem sSlots_eq_slotSet6
    (w : CountedOrderTypeGyration.VertexWord 8 8 6)
    (e : Fin 8 × Fin 8) :
    CountedOrderTypeGyration.SignedSupport.sSlots w e = slotSet6
      (fun t => (w.2 t, w.1 (t + 1))) e := by
  ext t
  fin_cases t <;>
    simp only [CountedOrderTypeGyration.SignedSupport.sSlots,
      Finset.mem_filter, Finset.mem_univ, true_and, slotSet6,
      Finset.mem_union, Finset.mem_singleton]
  all_goals split_ifs <;> simp_all

def rankWidthFast (w : CountedOrderTypeGyration.VertexWord 8 8 6)
    (l : Fin 6 → ℕ) (e : Fin 8 × Fin 8) : ℕ :=
  (slotSet6 (fun t => (w.2 t, w.1 (t + 1))) e).image l |>.card

def rankVectorsFast (S : Matrix (Fin 8) (Fin 8) ℤ)
    (w : CountedOrderTypeGyration.VertexWord 8 8 6) :
    Finset (Fin 6 → ℕ) :=
  (Fintype.piFinset fun t : Fin 6 =>
    Finset.range (if S (w.2 t) (w.1 (t+1)) = -1 then
      (slotSet6 (fun u => (w.2 u, w.1 (u + 1))
        ) (w.2 t, w.1 (t+1))).card else 1)).filter
    (fun l => ∀ t : Fin 6,
      l t < rankWidthFast w l (w.2 t, w.1 (t+1)))

theorem rankVectorsFast_eq
    (S : Matrix (Fin 8) (Fin 8) ℤ)
    (w : CountedOrderTypeGyration.VertexWord 8 8 6) :
    rankVectorsFast S w = rankVectors S w := by
  classical
  ext l
  unfold rankVectorsFast CountedOrderTypeGyration.SignedSupport.rankVectors
  constructor
  · intro hl
    rcases Finset.mem_filter.mp hl with ⟨hbox, hsurj⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · rw [Fintype.mem_piFinset] at hbox ⊢
      intro t
      simpa only [sSlots_eq_slotSet6] using hbox t
    · intro t
      simpa [rankWidthFast, CountedOrderTypeGyration.SignedSupport.rankWidth,
        sSlots_eq_slotSet6] using hsurj t
  · intro hl
    rcases Finset.mem_filter.mp hl with ⟨hbox, hsurj⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · rw [Fintype.mem_piFinset] at hbox ⊢
      intro t
      simpa only [sSlots_eq_slotSet6] using hbox t
    · intro t
      simpa [rankWidthFast, CountedOrderTypeGyration.SignedSupport.rankWidth,
        sSlots_eq_slotSet6] using hsurj t

def coefficientFast
    (S : Matrix (Fin 8) (Fin 8) ℤ)
    (w : CountedOrderTypeGyration.VertexWord 8 8 6)
    (l : Fin 6 → ℕ) : ℤ :=
  ∏ e : Fin 8 × Fin 8, if S e.1 e.2 = -1 then
    (-1 : ℤ)^(rankWidthFast w l e) else 1

theorem coefficientFast_eq
    (S : Matrix (Fin 8) (Fin 8) ℤ)
    (w : CountedOrderTypeGyration.VertexWord 8 8 6)
    (l : Fin 6 → ℕ) :
    coefficientFast S w l =
      CountedOrderTypeGyration.SignedSupport.coefficient S w l := by
  classical
  unfold coefficientFast CountedOrderTypeGyration.SignedSupport.coefficient
  apply Finset.prod_congr rfl
  intro e _
  by_cases h : S e.1 e.2 = -1 <;> simp [h, rankWidthFast,
    CountedOrderTypeGyration.SignedSupport.rankWidth,
    ← sSlots_eq_slotSet6]

def vectorTermFast
    (S : Matrix (Fin 8) (Fin 8) ℤ)
    (w : CountedOrderTypeGyration.VertexWord 8 8 6)
    (l : Fin 6 → ℕ) : ℤ :=
  keyWeight (sourceKeys w l) (targetKeys w l) * coefficientFast S w l

theorem vectorTermFast_eq
    (S : Matrix (Fin 8) (Fin 8) ℤ)
    (w : CountedOrderTypeGyration.VertexWord 8 8 6)
    (l : Fin 6 → ℕ) :
    vectorTermFast S w l = vectorTerm S w l := by
  simp [vectorTermFast, vectorTerm, coefficientFast_eq]

/- A fixed six-slot decision form for the two lexical tests used by the
   period-six evaluator.  It keeps the same rank-labelled keys, but avoids
   the generic finite existential/rotation reduction in every leaf. -/
def keyWordLT6 (a b : Fin 6 → Key) : Prop :=
  KeyLT (a 0) (b 0) ∨
    (a 0 = b 0 ∧ KeyLT (a 1) (b 1)) ∨
    (a 0 = b 0 ∧ a 1 = b 1 ∧ KeyLT (a 2) (b 2)) ∨
    (a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 ∧ KeyLT (a 3) (b 3)) ∨
    (a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 ∧ a 3 = b 3 ∧ KeyLT (a 4) (b 4)) ∨
    (a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 ∧ a 3 = b 3 ∧ a 4 = b 4 ∧
      KeyLT (a 5) (b 5))

def keyWordLT6Decide (a b : Fin 6 → Key) : Decidable (keyWordLT6 a b) := by
  by_cases h0 : KeyLT (a 0) (b 0)
  · exact isTrue (Or.inl h0)
  · by_cases h1 : a 0 = b 0 ∧ KeyLT (a 1) (b 1)
    · exact isTrue (Or.inr (Or.inl h1))
    · by_cases h2 : a 0 = b 0 ∧ a 1 = b 1 ∧ KeyLT (a 2) (b 2)
      · exact isTrue (Or.inr (Or.inr (Or.inl h2)))
      · by_cases h3 : a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 ∧ KeyLT (a 3) (b 3)
        · exact isTrue (Or.inr (Or.inr (Or.inr (Or.inl h3))))
        · by_cases h4 : a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 ∧ a 3 = b 3 ∧
            KeyLT (a 4) (b 4)
          · exact isTrue (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4)))))
          · by_cases h5 : a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 ∧ a 3 = b 3 ∧
              a 4 = b 4 ∧ KeyLT (a 5) (b 5)
            · exact isTrue (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h5)))))
            · exact isFalse (by
                intro h
                rcases h with h | h | h | h | h | h
                · exact h0 h
                · exact h1 h
                · exact h2 h
                · exact h3 h
                · exact h4 h
                · exact h5 h)

local instance keyWordLT6_decidable (a b : Fin 6 → Key) : Decidable (keyWordLT6 a b) :=
  keyWordLT6Decide a b

def rotate6 (k : Fin 6) (a : Fin 6 → Key) : Fin 6 → Key :=
  fun t => a (t + k)

def keyLeast6 (a : Fin 6 → Key) : Prop :=
  keyWordLT6 a (rotate6 1 a) ∧
    keyWordLT6 a (rotate6 2 a) ∧
    keyWordLT6 a (rotate6 3 a) ∧
    keyWordLT6 a (rotate6 4 a) ∧
    keyWordLT6 a (rotate6 5 a)

def keyLeast6Decide (a : Fin 6 → Key) : Decidable (keyLeast6 a) := by
  unfold keyLeast6
  infer_instance

local instance keyLeast6_decidable (a : Fin 6 → Key) : Decidable (keyLeast6 a) :=
  keyLeast6Decide a

theorem keyWordLT6_eq (a b : Fin 6 → Key) :
    keyWordLT6 a b = KeyWordLT a b := by
  apply propext
  constructor
  · intro h
    rcases h with h | h | h | h | h | h
    · exact ⟨0, by intro u hu; omega, h⟩
    · refine ⟨1, ?_, h.2⟩
      intro u hu
      fin_cases u <;> simp_all
    · refine ⟨2, ?_, h.2.2⟩
      intro u hu
      fin_cases u <;> simp_all
    · refine ⟨3, ?_, h.2.2.2⟩
      intro u hu
      fin_cases u <;> simp_all
    · refine ⟨4, ?_, h.2.2.2.2⟩
      intro u hu
      fin_cases u <;> simp_all
    · refine ⟨5, ?_, h.2.2.2.2.2⟩
      intro u hu
      fin_cases u <;> simp_all
  · rintro ⟨t, hp, ht⟩
    fin_cases t
    · exact Or.inl ht
    · have h0 : a 0 = b 0 := by simpa using hp 0 (by decide)
      have ht' : KeyLT (a 1) (b 1) := by simpa using ht
      exact Or.inr (Or.inl ⟨h0, ht'⟩)
    · have h0 : a 0 = b 0 := by simpa using hp 0 (by decide)
      have h1 : a 1 = b 1 := by simpa using hp 1 (by decide)
      have ht' : KeyLT (a 2) (b 2) := by simpa using ht
      exact Or.inr (Or.inr (Or.inl ⟨h0, h1, ht'⟩))
    · have h0 : a 0 = b 0 := by simpa using hp 0 (by decide)
      have h1 : a 1 = b 1 := by simpa using hp 1 (by decide)
      have h2 : a 2 = b 2 := by simpa using hp 2 (by decide)
      have ht' : KeyLT (a 3) (b 3) := by simpa using ht
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1, h2, ht'⟩)))
    · have h0 : a 0 = b 0 := by simpa using hp 0 (by decide)
      have h1 : a 1 = b 1 := by simpa using hp 1 (by decide)
      have h2 : a 2 = b 2 := by simpa using hp 2 (by decide)
      have h3 : a 3 = b 3 := by simpa using hp 3 (by decide)
      have ht' : KeyLT (a 4) (b 4) := by simpa using ht
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1, h2, h3, ht'⟩))))
    · have h0 : a 0 = b 0 := by simpa using hp 0 (by decide)
      have h1 : a 1 = b 1 := by simpa using hp 1 (by decide)
      have h2 : a 2 = b 2 := by simpa using hp 2 (by decide)
      have h3 : a 3 = b 3 := by simpa using hp 3 (by decide)
      have h4 : a 4 = b 4 := by simpa using hp 4 (by decide)
      have ht' : KeyLT (a 5) (b 5) := by simpa using ht
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h0, h1, h2, h3, h4, ht'⟩))))

theorem rotate6_eq (k : Fin 6) (a : Fin 6 → Key) :
    rotate6 k a = CountedOrderTypeGyration.rotate k a := by
  rfl

theorem keyLeast6_eq (a : Fin 6 → Key) :
    keyLeast6 a ↔ KeyLeast a := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩ k hk
    fin_cases k
    · exact (hk rfl).elim
    · have hh := (keyWordLT6_eq a (rotate6 1 a)).mp h1
      rw [rotate6_eq] at hh
      exact hh
    · have hh := (keyWordLT6_eq a (rotate6 2 a)).mp h2
      rw [rotate6_eq] at hh
      exact hh
    · have hh := (keyWordLT6_eq a (rotate6 3 a)).mp h3
      rw [rotate6_eq] at hh
      exact hh
    · have hh := (keyWordLT6_eq a (rotate6 4 a)).mp h4
      rw [rotate6_eq] at hh
      exact hh
    · have hh := (keyWordLT6_eq a (rotate6 5 a)).mp h5
      rw [rotate6_eq] at hh
      exact hh
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply (keyWordLT6_eq a (rotate6 1 a)).mpr
      have hh := h 1 (by decide)
      rw [← rotate6_eq] at hh
      exact hh
    · apply (keyWordLT6_eq a (rotate6 2 a)).mpr
      have hh := h 2 (by decide)
      rw [← rotate6_eq] at hh
      exact hh
    · apply (keyWordLT6_eq a (rotate6 3 a)).mpr
      have hh := h 3 (by decide)
      rw [← rotate6_eq] at hh
      exact hh
    · apply (keyWordLT6_eq a (rotate6 4 a)).mpr
      have hh := h 4 (by decide)
      rw [← rotate6_eq] at hh
      exact hh
    · apply (keyWordLT6_eq a (rotate6 5 a)).mpr
      have hh := h 5 (by decide)
      rw [← rotate6_eq] at hh
      exact hh

def keyWeightFast6 (a b : Fin 6 → Key) : ℤ :=
  if keyLeast6 a then
    ∑ k : Fin 6, if keyLeast6 (rotate6 k b) then -(k.val : ℤ) else 0
  else 0

theorem keyWeightFast6_eq (a b : Fin 6 → Key) :
    keyWeightFast6 a b = keyWeight a b := by
  unfold keyWeightFast6 keyWeight
  by_cases h : keyLeast6 a
  · have h' : KeyLeast a := (keyLeast6_eq a).mp h
    simp only [if_pos h, if_pos h']
    apply Finset.sum_congr rfl
    intro k _
    have hk : keyLeast6 (rotate6 k b) ↔ KeyLeast (CountedOrderTypeGyration.rotate k b) := by
      rw [keyLeast6_eq, rotate6_eq]
    exact if_congr hk rfl rfl
  · have h' : ¬ KeyLeast a := by
      intro ha
      exact h ((keyLeast6_eq a).mpr ha)
    simp only [if_neg h, if_neg h']

def vectorTermFast6
    (S : Matrix (Fin 8) (Fin 8) ℤ)
    (w : CountedOrderTypeGyration.VertexWord 8 8 6)
    (l : Fin 6 → ℕ) : ℤ :=
  keyWeightFast6 (sourceKeys w l) (targetKeys w l) * coefficientFast S w l

theorem vectorTermFast6_eq
    (S : Matrix (Fin 8) (Fin 8) ℤ)
    (w : CountedOrderTypeGyration.VertexWord 8 8 6)
    (l : Fin 6 → ℕ) :
    vectorTermFast6 S w l = vectorTerm S w l := by
  simp [vectorTermFast6, vectorTerm, keyWeightFast6_eq, coefficientFast_eq]

/- The time matrix has the same one-middle-word reduction as the original
   shard, but its zero-binomial leaves can use the fixed six-slot lexical
   decision form above. -/
def fastTimeShardFast (i : Fin 8) : ℤ :=
  ∑ tail : Fin 5 → Fin 8,
    let a : Fin 6 → Fin 8 := Fin.cons i tail
    if h : validAdj6 originalAdjacency a then
      keyWeightFast6 (sourceKeys (a, nextWord a) zeroRanks)
        (targetKeys (a, nextWord a) zeroRanks)
    else 0


def onePlusShardLeafOriginal (i j k : Fin 8) : ℤ :=
  ∑ tail ∈ (Finset.univ.filter (fun tail : Fin 3 → Fin 8 =>
      (middleWords (1 + originalAdjacency) onePlusSignedFactor
        (Fin.cons i (Fin.cons j (Fin.cons k tail)))).Nonempty)),
    ∑ b ∈ (middleWords (1 + originalAdjacency) onePlusSignedFactor
      (Fin.cons i (Fin.cons j (Fin.cons k tail)))).filter
        (fun b => SkeletonMinimal
          (Fin.cons i (Fin.cons j (Fin.cons k tail)), b)),
      ∑ l' ∈ rankVectors onePlusSignedFactor
          (Fin.cons i (Fin.cons j (Fin.cons k tail)), b),
        vectorTerm onePlusSignedFactor
          (Fin.cons i (Fin.cons j (Fin.cons k tail)), b) l'


def onePlusShardLeaf (i j k : Fin 8) : ℤ :=
  ∑ tail ∈ (Finset.univ.filter (fun tail : Fin 3 → Fin 8 =>
      sourceMinimal6Fast (Fin.cons i (Fin.cons j (Fin.cons k tail))) ∧
        pathValid6Fast (Fin.cons i (Fin.cons j (Fin.cons k tail))))),
    ∑ b ∈ (onePlusMiddleWords (Fin.cons i (Fin.cons j (Fin.cons k tail)))).filter
        (fun b => skeletonMinimal6Fast
          (Fin.cons i (Fin.cons j (Fin.cons k tail)), b)),
      ∑ l' ∈ rankVectorsFast onePlusSignedFactor
          (Fin.cons i (Fin.cons j (Fin.cons k tail)), b),
        vectorTermFast6 onePlusSignedFactor
          (Fin.cons i (Fin.cons j (Fin.cons k tail)), b) l'


theorem onePlusShardLeaf_eq_original (i j k : Fin 8) :
    onePlusShardLeaf i j k = onePlusShardLeafOriginal i j k := by
  classical
  let fastBody : (Fin 3 → Fin 8) → ℤ := fun tail =>
    ∑ b ∈ (onePlusMiddleWords (Fin.cons i (Fin.cons j (Fin.cons k tail)))).filter
        (fun b => skeletonMinimal6Fast
          (Fin.cons i (Fin.cons j (Fin.cons k tail)), b)),
      ∑ l' ∈ rankVectorsFast onePlusSignedFactor
          (Fin.cons i (Fin.cons j (Fin.cons k tail)), b),
        vectorTermFast6 onePlusSignedFactor
          (Fin.cons i (Fin.cons j (Fin.cons k tail)), b) l'
  let oldBody : (Fin 3 → Fin 8) → ℤ := fun tail =>
    ∑ b ∈ (middleWords (1 + originalAdjacency) onePlusSignedFactor
      (Fin.cons i (Fin.cons j (Fin.cons k tail)))).filter
        (fun b => SkeletonMinimal
          (Fin.cons i (Fin.cons j (Fin.cons k tail)), b)),
      ∑ l' ∈ rankVectors onePlusSignedFactor
          (Fin.cons i (Fin.cons j (Fin.cons k tail)), b),
        vectorTerm onePlusSignedFactor
          (Fin.cons i (Fin.cons j (Fin.cons k tail)), b) l'
  have hfast (tail : Fin 3 → Fin 8) : fastBody tail = oldBody tail := by
    let a : Fin 6 → Fin 8 := Fin.cons i (Fin.cons j (Fin.cons k tail))
    by_cases hs : sourceMinimal6Fast a
    · have hsOld : sourceMinimal a := (sourceMinimal6Fast_iff a).mp hs
      by_cases hp : pathValid6Fast a
      · simp only [fastBody, oldBody, onePlusMiddleWords_eq]
        simp_rw [skeletonMinimal6Fast_iff, rankVectorsFast_eq, vectorTermFast6_eq]
      · have he : onePlusMiddleWords a = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hne
          obtain ⟨b, hb⟩ := hne
          rw [onePlusMiddleWords, Fintype.mem_piFinset] at hb
          have hnot : ¬ ∀ t : Fin 6,
              (onePlusMiddleFiber (a t) (a (t + 1))).Nonempty := by
            intro hall
            exact hp ((pathValid6Fast_iff a).mpr hall)
          obtain ⟨t, ht⟩ := not_forall.mp hnot
          exact ht ⟨b t, by simpa [a] using hb t⟩
        have ho : middleWords (1 + originalAdjacency) onePlusSignedFactor a = ∅ := by
          rw [← onePlusMiddleWords_eq]
          exact he
        simp [fastBody, oldBody, he, ho, a]
    · have hsOld : ¬ sourceMinimal a := by
        intro h
        exact hs ((sourceMinimal6Fast_iff a).mpr h)
      have hsourceFast : fastBody tail = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        have hbmin := (Finset.mem_filter.mp hb).2
        obtain ⟨t, ht⟩ := not_forall.mp hsOld
        have hlt : sourcePairLT a t := by by_contra hnot; exact ht hnot
        have hbminOld : SkeletonMinimal (a, b) :=
          (skeletonMinimal6Fast_iff (a, b)).mp hbmin
        exact False.elim (hbminOld t (sourcePairLT_skeleton hlt))
      have hsourceOld : oldBody tail = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        have hbmin := (Finset.mem_filter.mp hb).2
        obtain ⟨t, ht⟩ := not_forall.mp hsOld
        have hlt : sourcePairLT a t := by by_contra hnot; exact ht hnot
        exact False.elim (hbmin t (sourcePairLT_skeleton hlt))
      rw [hsourceFast, hsourceOld]
  calc
    onePlusShardLeaf i j k =
        ∑ tail : Fin 3 → Fin 8, fastBody tail := by
      unfold onePlusShardLeaf
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro tail _ hnot
      have hcond : ¬ (sourceMinimal6Fast (Fin.cons i (Fin.cons j (Fin.cons k tail))) ∧
          pathValid6Fast (Fin.cons i (Fin.cons j (Fin.cons k tail)))) := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot
      by_cases hs : sourceMinimal6Fast (Fin.cons i (Fin.cons j (Fin.cons k tail)))
      · have hp : ¬ pathValid6Fast (Fin.cons i (Fin.cons j (Fin.cons k tail))) := by
          intro hp
          exact hcond ⟨hs, hp⟩
        have he : onePlusMiddleWords (Fin.cons i (Fin.cons j (Fin.cons k tail))) = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hne
          obtain ⟨b, hb⟩ := hne
          rw [onePlusMiddleWords, Fintype.mem_piFinset] at hb
          let a : Fin 6 → Fin 8 := Fin.cons i (Fin.cons j (Fin.cons k tail))
          have hnot : ¬ ∀ t : Fin 6,
              (onePlusMiddleFiber (a t) (a (t + 1))).Nonempty := by
            intro hall
            exact hp ((pathValid6Fast_iff a).mpr hall)
          obtain ⟨t, ht⟩ := not_forall.mp hnot
          exact ht ⟨b t, by simpa [a] using hb t⟩
        simp [fastBody, he]
      · have hsourceFast : fastBody tail = 0 := by
          have hsOld : ¬ sourceMinimal (Fin.cons i (Fin.cons j (Fin.cons k tail))) := by
            intro h
            exact hs ((sourceMinimal6Fast_iff _).mpr h)
          apply Finset.sum_eq_zero
          intro b hb
          have hbmin := (Finset.mem_filter.mp hb).2
          obtain ⟨t, ht⟩ := not_forall.mp hsOld
          have hlt : sourcePairLT (Fin.cons i (Fin.cons j (Fin.cons k tail))) t := by
            by_contra hnot
            exact ht hnot
          have hbminOld : SkeletonMinimal
              (Fin.cons i (Fin.cons j (Fin.cons k tail)), b) :=
            (skeletonMinimal6Fast_iff
              (Fin.cons i (Fin.cons j (Fin.cons k tail)), b)).mp hbmin
          exact False.elim (hbminOld t (sourcePairLT_skeleton hlt))
        exact hsourceFast
    _ = ∑ tail : Fin 3 → Fin 8, oldBody tail := by
      apply Finset.sum_congr rfl
      intro tail _
      exact hfast tail
    _ = onePlusShardLeafOriginal i j k := by
      unfold onePlusShardLeafOriginal
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro tail _ hnot
      have ho : ¬ (middleWords (1 + originalAdjacency) onePlusSignedFactor
          (Fin.cons i (Fin.cons j (Fin.cons k tail)))).Nonempty := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot
      have he := Finset.not_nonempty_iff_eq_empty.mp ho
      simp [oldBody, he]

theorem prunedShard_onePlus_eq_split3 (i : Fin 8) :
    prunedShard 5 (1 + originalAdjacency) onePlusSignedFactor i =
      ∑ j : Fin 8, ∑ k : Fin 8, onePlusShardLeaf i j k := by
  classical
  let body : (Fin 5 → Fin 8) → ℤ := fun tail =>
    ∑ b ∈ (middleWords (1 + originalAdjacency) onePlusSignedFactor
      (Fin.cons i tail)).filter
        (fun b => SkeletonMinimal (Fin.cons i tail, b)),
      ∑ l ∈ rankVectors onePlusSignedFactor (Fin.cons i tail, b),
        vectorTerm onePlusSignedFactor (Fin.cons i tail, b) l
  calc
    prunedShard 5 (1 + originalAdjacency) onePlusSignedFactor i =
        ∑ tail : Fin 5 → Fin 8, body tail := by
      rfl
    _ = ∑ j : Fin 8, ∑ tail : Fin 4 → Fin 8,
        body (Fin.cons j tail) := by
      exact sumConsFin8 body
    _ = ∑ j : Fin 8, ∑ k : Fin 8, ∑ tail : Fin 3 → Fin 8,
        body (Fin.cons j (Fin.cons k tail)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact sumConsFin8 (fun tail : Fin 4 → Fin 8 => body (Fin.cons j tail))
    _ = ∑ j : Fin 8, ∑ k : Fin 8, onePlusShardLeafOriginal i j k := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      unfold onePlusShardLeafOriginal
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro tail _ hnot
      have ho : ¬ (middleWords (1 + originalAdjacency) onePlusSignedFactor
          (Fin.cons i (Fin.cons j (Fin.cons k tail)))).Nonempty := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot
      have he := Finset.not_nonempty_iff_eq_empty.mp ho
      simp [body, he]
    _ = ∑ j : Fin 8, ∑ k : Fin 8, onePlusShardLeaf i j k := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      exact (onePlusShardLeaf_eq_original i j k).symm

def onePlusChunkValue : Fin 8 → Fin 8 → Fin 8 → ℤ :=
  ![  ![    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![-9, 0, 8, -3, -5, 2, 2, -2],
    ![0, -6, 0, 0, -3, -3, 0, 0],
    ![0, 0, -2, 0, 2, -7, -2, 3],
    ![0, 5, 0, -2, 0, 0, 0, 0],
    ![-2, 0, 2, 0, -2, 0, 2, -3],
    ![0, -8, 0, -2, 0, 2, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0]
  ],
  ![    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -1, 0, 2, -6, 4, 0, -4],
    ![0, 0, -5, 0, 0, -5, 0, 0],
    ![0, -1, 0, -8, 0, 0, -3, 0],
    ![0, 0, 1, 0, -3, 0, 2, 5],
    ![0, 4, 0, 8, 0, 0, 0, 0],
    ![0, 0, -5, 0, 7, 0, -2, 0]
  ],
  ![    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -4, 0, 2, 2, -2, 0],
    ![0, 0, 0, -4, 0, 2, 2, -2],
    ![0, 0, -2, 0, 0, 0, 0, -3],
    ![0, 0, 0, 1, 0, 2, 0, 2],
    ![0, 0, -4, 0, 4, 0, -4, 0]
  ],
  ![    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -1, 0, -1, 2, 0],
    ![0, 0, 0, 0, 2, 0, -3, 0],
    ![0, 0, 0, 2, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0]
  ],
  ![    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -4, 0, 0, 7],
    ![0, 0, 0, 0, 0, -12, 0, 2],
    ![0, 0, 0, 0, 0, 0, 2, 0]
  ],
  ![    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 4, 0, -6],
    ![0, 0, 0, 0, 0, 0, 5, 0]
  ],
  ![    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, -4, 0]
  ],
  ![    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0]
  ]
]

theorem onePlusShardLeaf_eq_zero_of_middle_empty (i j k : Fin 8)
    (h : onePlusMiddleFiber i j = ∅ ∨ onePlusMiddleFiber j k = ∅) :
    onePlusShardLeaf i j k = 0 := by
  classical
  unfold onePlusShardLeaf
  apply Finset.sum_eq_zero
  intro tail htail
  have hp := (Finset.mem_filter.mp htail).2.2
  rcases h with h | h
  · have hp0 := hp.1
    have hp0' : (onePlusMiddleFiber i j).Nonempty := by
      simpa [pathValid6Fast] using hp0
    simpa [h] using hp0'
  · let a : Fin 6 → Fin 8 := Fin.cons i (Fin.cons j (Fin.cons k tail))
    have hp' : pathValid6Fast a := by simpa [a] using hp
    have hp1 := hp'.2.1
    have hidx : (1 + 1 : Fin 6) = 2 := by decide
    rw [hidx] at hp1
    have ha2 : a (2 : Fin 6) = k := by
      change ((Fin.cons i (Fin.cons j (Fin.cons k tail)) : Fin 6 → Fin 8)
        (2 : Fin 6)) = k
      rw [show (2 : Fin 6) = Fin.succ (1 : Fin 5) by decide]
      rw [Fin.cons_succ]
      rw [show (1 : Fin 5) = Fin.succ (0 : Fin 4) by decide]
      rw [Fin.cons_succ, Fin.cons_zero]
    rw [ha2] at hp1
    have hp1' : (onePlusMiddleFiber j k).Nonempty := by
      simpa [a] using hp1
    simpa [h] using hp1'

theorem onePlusShardLeaf_eq_zero_of_source_pair (i j k : Fin 8)
    (h : sourcePairLT
        (Fin.cons i (Fin.cons j (Fin.cons k (fun _ => 0)))) 1 ∨
      k.val < i.val) :
    onePlusShardLeaf i j k = 0 := by
  classical
  unfold onePlusShardLeaf
  apply Finset.sum_eq_zero
  intro tail htail
  let a : Fin 6 → Fin 8 := Fin.cons i (Fin.cons j (Fin.cons k tail))
  have hs := (Finset.mem_filter.mp htail).2.1
  have hs' : sourceMinimal6Fast a := by
    simpa [a] using hs
  rcases h with h | h
  · have h' : sourcePairLT a 1 := by
      unfold sourcePairLT at h ⊢
      change (j.val < i.val ∨ (j.val = i.val ∧ k.val < j.val)) at h ⊢
      exact h
    exact (hs'.2.1 h').elim
  · have h' : sourcePairLT a 2 := by
      unfold sourcePairLT
      left
      have ha2 : a (2 : Fin 6) = k := by
        change ((Fin.cons i (Fin.cons j (Fin.cons k tail)) : Fin 6 → Fin 8)
          (2 : Fin 6)) = k
        rw [show (2 : Fin 6) = Fin.succ (1 : Fin 5) by decide]
        rw [Fin.cons_succ]
        rw [show (1 : Fin 5) = Fin.succ (0 : Fin 4) by decide]
        rw [Fin.cons_succ, Fin.cons_zero]
      have ha0 : a (0 : Fin 6) = i := by simp [a]
      rw [ha2, ha0]
      exact h
    exact (hs'.2.2.1 h').elim

end D5.S3.ConceptDynamics.Coding

