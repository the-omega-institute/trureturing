/- GID: D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial
   generality: I
   mirror-B: none
   mirror-E: none(waiver:stage-a-open)
   anchors: []
   utility: none
   digest: The native diagonal-to-slice polynomial bridge is stated explicitly, with its conditional slice-readout consequence. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.CopyProfilePolynomial

open D5.S0.History.Spacetime.ArchiveCarrier
open D5.S3.ConceptDynamics.Observation.StrictOneHoleContexts
open private selected_region_values from D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility
open ComplementCharge TotalCopyNormalization RegionFilterQExpressibility
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Bal := TotalCopyNormalization.B

/-- The diagonal operation that supplies `m` tagged parallel copies of one input. -/
def copies : Nat → Bal → Bal
  | 0, _ => zero
  | n + 1, X => ParallelComposition.parallelBalanced (copies n X) X

/-- The total value of a copy term under an arbitrary independent assignment. -/
def value {r : Nat} (N : CopyTerm r) (v : Fin r → Bal) : Bal :=
  (eval N v).getD zero

/--
The 5B/5C bridge required by the copy argument.  It says that a temporal-free
term, evaluated on independently replicated leaves, has an integer polynomial
profile.  The displayed coefficient is the full 5C coefficient and retains the
constant correction `- r * q(N(0))`.
-/
def CopyPolynomialLaw : Prop := ∀ (r : Nat) (N : CopyTerm r), 0 < r → TemporalFree N →
  ∀ X : Bal, ∃ P : Polynomial Int,
    P.natDegree ≤ r ∧
    (∀ n : Nat, P.eval (n : Int) = q (value N (fun _ => copies n X)).val) ∧
    P.coeff 0 = q (zeroValue N).val ∧
    P.coeff 1 = (∑ i : Fin r, q (value N (sliceAssignment i X)).val) -
      (r : Int) * q (zeroValue N).val

/-- Parallel replication is linear for every fixed region readout. -/
def CopiesRegionLinear : Prop := ∀ (R : Region) (n : Nat) (X : Bal),
  regionReadout R (copies n X) = (n : Int) * regionReadout R X

/-- A readout of a total one-hole word, with failure assigned the neutral integer. -/
def wordReadout (w : Word) (X : Bal) : Int :=
  ((contextDenote nativeSignature w X).map (fun Y => q Y.val)).getD 0

/--
The post-polynomial normalization statement needed by the tail argument.  It
keeps the exact finite family of temporal-free one-hole words and the exact
sum of their readouts.  This is a named open obligation rather than an axiom.
-/
def CopySliceReadoutLaw : Prop := ∀ (R : Region) (n : Nat) (C : CopyTerm n), 0 < n →
  DiagonalTotal C →
  (∀ X : Bal, ∃ Y : Bal, evalDiagonal C X = some Y ∧ q Y.val = regionReadout R X) →
  ∃ w : Fin n → Word,
    (∀ i, ∀ X : Bal, ∃ Y : Bal, contextDenote nativeSignature (w i) X = some Y) ∧
    ∀ X : Bal, regionReadout R X = ∑ i, wordReadout (w i) X

/-- The finite joint saturation principle used after slice normalization. -/
def CopySaturationLaw : Prop := ∀ {ι : Type} [Fintype ι] (w : ι → Word),
  (∀ i, ∀ X : Bal, ∃ Y : Bal, contextDenote nativeSignature (w i) X = some Y) →
  ∃ c : Int, ∀ (p : Fin 3 → Int) (t t' : Int), t < c → t' < c →
    ∃ X Y : Bal, SelectedVariant X Y p t t' ∧
      ∀ i, wordReadout (w i) X = wordReadout (w i) Y

/-- The copy form of Proposition 64. -/
def CopyQExpressible (R : Region) : Prop := ∃ n : Nat, 0 < n ∧ ∃ C : CopyTerm n,
  DiagonalTotal C ∧ ∀ X : Bal, ∃ Y : Bal,
    evalDiagonal C X = some Y ∧ q Y.val = regionReadout R X

/-- Polynomial identification from all natural evaluations. -/
theorem polynomial_identification (P : Polynomial Int) (a : Int)
    (h : ∀ n : Nat, P.eval (n : Int) = (n : Int) * a) :
    P = Polynomial.X * Polynomial.C a := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective Int.ofNat_injective).mono
  rintro _ ⟨n, rfl⟩
  simpa using h n

/-- A finite sum of total word readouts is a tail readout. -/
theorem sum_word_readouts_implies_tail
    (hSat : CopySaturationLaw) (R : Region) {ι : Type} [Fintype ι]
    (w : ι → Word)
    (hw : ∀ i, ∀ X : Bal, ∃ Y : Bal, contextDenote nativeSignature (w i) X = some Y)
    (hsum : ∀ X : Bal, regionReadout R X = ∑ i, wordReadout (w i) X) : Tail R := by
  obtain ⟨c, hc⟩ := hSat (ι := ι) w hw
  refine ⟨c, fun p t t' ht ht' => ?_⟩
  obtain ⟨X, Y, pair, same⟩ := hc p t t' ht ht'
  have values : regionReadout R X = regionReadout R Y := by
    rw [hsum X, hsum Y]
    exact Finset.sum_congr rfl (fun i _ => same i)
  obtain ⟨hX, hY⟩ := selected_region_values R X Y p t t' pair
  rw [hX, hY] at values
  split_ifs at values <;> simp_all

/-- Conditional necessity of the copy criterion. -/
theorem copy_q_expressible_implies_tail
    (hSlice : CopySliceReadoutLaw) (hSat : CopySaturationLaw)
    (R : Region) (hR : CopyQExpressible R) : Tail R := by
  obtain ⟨n, hn, C, ht, hC⟩ := hR
  obtain ⟨w, hw, hsum⟩ := hSlice R n C hn ht hC
  exact sum_word_readouts_implies_tail hSat R w hw hsum

/-- Tail regions are copy-expressible by the existing one-hole construction. -/
theorem tail_implies_copy_q_expressible (R : Region) (hR : Tail R) :
    CopyQExpressible R := by
  obtain ⟨w, hw⟩ := (q_expressible_iff_tail R).mpr hR
  refine ⟨1, by decide, wordToCopy w, ?_, ?_⟩
  · intro X
    obtain ⟨Y, hY, _⟩ := hw X
    exact ⟨Y, by simpa only [word_to_copy_denote] using hY⟩
  · intro X
    obtain ⟨Y, hY, hq⟩ := hw X
    exact ⟨Y, by simpa only [word_to_copy_denote] using hY, hq⟩

end
end D5.S3.ConceptDynamics.Spacetime.CopyProfilePolynomial
