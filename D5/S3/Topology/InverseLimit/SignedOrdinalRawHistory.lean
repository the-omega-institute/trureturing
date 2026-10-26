/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalRawHistory
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalRawHistory
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Concrete original births and historical capture data on the realized run diagram. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalRealization

/-! RawHistory retains the original whole births, reservoirs and incoming J. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalRawHistory

open SignedProperLimit SignedBirthEnumeration SignedOrdinalSuccessor
open SignedOrdinalHistoryEvent SignedOrdinalHistoryBirth SignedOrdinalHistoryState
open SignedOrdinalRealization SignedBallHistoryCapture
open D5.S3.Topology.Measures

variable (hCH : Cardinal.continuum.{0} = ℵ₁)

private theorem reservoirs (θ : Stage) (d : Label) :
    Disjoint (reservoir hCH θ d false) (reservoir hCH θ d true) := by
  exact (SignedOrdinalHistory.run hCH
    ⟨max θ.1 d, θ.2.trans (le_max_left _ _)⟩).event.result.B _ _

private theorem infinite (θ : Stage) (d : Label) (c : Eligible θ d) (e : Bool) :
    (historicalJ hCH θ d c ∩ reservoir hCH θ d e).Infinite := by
  let C : Stage := ⟨c.1, θ.2.trans ((le_max_left _ _).trans c.2.le)⟩
  let hθ : θ < C := (le_max_left _ _).trans_lt c.2
  let hd : d.1 < ord C := (le_max_right _ _).trans_lt c.2
  rw [reservoir_incoming hCH θ d C hθ hd]
  exact (SignedOrdinalHistory.run hCH C).P.C _ _ _ (if e then 1 else 0)

private theorem directed (θ : Stage) (d : Label) (b c : Eligible θ d)
    (hbc : b.1 ≤ c.1) :
    (historicalJ hCH θ d c \ historicalJ hCH θ d b).Finite := by
  have hs : AlmostSubset (historicalJ hCH θ d c) (historicalJ hCH θ d b) := by
    rcases hbc.eq_or_lt with he | hlt
    · have he' : b = c := Subtype.ext he
      subst c
      exact Filter.Eventually.of_forall (fun _ hn => hn)
    · let B : Stage := ⟨b.1, θ.2.trans ((le_max_left _ _).trans b.2.le)⟩
      let C : Stage := ⟨c.1, θ.2.trans ((le_max_left _ _).trans c.2.le)⟩
      let hθ : θ < B := (le_max_left _ _).trans_lt b.2
      exact (SignedOrdinalHistory.coherent hCH B C hlt).DJ
        (oldRow hθ (newRow (ord θ) θ.2)) (oldRow_ne hθ _)
        ⟨d.1, (le_max_right _ _).trans_lt b.2⟩
  simpa only [not_imp, mem_sdiff] using Filter.eventually_cofinite.mp hs

private theorem regular_f (θ : Stage) (d : Label) (c : Eligible θ d)
    (s : ℕ → SignedMeasure ((finalPrefix hCH).Space c.1))
    (hreg : ∀ n, (s n).totalVariation.Regular)
    (hn : ∀ n, (s n).totalVariation univ = 1)
    (hm : ∀ n, (s n).map
      ((finalPrefix hCH).map θ.1 c.1 ((le_max_left _ _).trans c.2.le)) =
        (((wholeBirth hCH θ).nu d).1 n).1) :
    ∃ μ : SignedMeasure ((finalPrefix hCH).Space c.1), μ.totalVariation.Regular ∧
      μ.totalVariation univ ≤ 1 ∧ ∀ g : C((finalPrefix hCH).Space c.1, ℝ),
        Tendsto (fun n => NormPreservingLifts.signedFunctional (s n) g)
          (cofinite ⊓ 𝓟 (historicalJ hCH θ d c))
          (𝓝 (NormPreservingLifts.signedFunctional μ g)) := by
  let hl : Order.succ c.1.1 < ω₁ := (Cardinal.isSuccLimit_omega 1).succ_lt c.1.2
  let r : Coord (Order.succ c.1.1) :=
    ⟨ord θ, ((le_max_left _ _).trans_lt c.2).trans (Order.lt_succ _)⟩
  let dd : Coord (Order.succ c.1.1) :=
    ⟨d.1, ((le_max_right _ _).trans_lt c.2).trans (Order.lt_succ _)⟩
  let cc : Coord (Order.succ c.1.1) := top c.1.1
  let seq : ℕ → RegularSigned ((properSlice hCH hl).Space cc) := fun n =>
    ⟨s n, by
      letI := hreg n
      exact RegularSignedLift.regular_jordanParts_of_regular_totalVariation _⟩
  have hclass (n : ℕ) :
      (properSlice hCH hl).OldClass (properData hCH hl) r dd cc
        (show r < cc from (le_max_left _ _).trans_lt c.2).le n (seq n) := by
    refine ⟨hn n, ?_⟩
    rw [slice_nu hCH hl r θ.2]
    exact hm n
  obtain ⟨mu, hb, hc⟩ := (properLaws hCH hl).F r dd cc
    ((le_max_left _ _).trans_lt c.2) θ.2 ((le_max_right _ _).trans_lt c.2) seq hclass
  let C : Stage := ⟨c.1, θ.2.trans ((le_max_left _ _).trans c.2.le)⟩
  let hθ : θ < C := (le_max_left _ _).trans_lt c.2
  have hj : (properData hCH hl).J r dd cc = historicalJ hCH θ d c :=
    slice_J hCH hl C (Order.lt_succ _) _ (oldRow_ne hθ _) _
  rw [hj] at hc
  letI : mu.1.toJordanDecomposition.posPart.Regular := mu.2.1
  letI : mu.1.toJordanDecomposition.negPart.Regular := mu.2.2
  refine ⟨mu.1, ?_, ?_, ?_⟩
  · change (mu.1.toJordanDecomposition.posPart + mu.1.toJordanDecomposition.negPart).Regular
    infer_instance
  · exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by norm_num)).mp
      (by simpa only [Measure.real, ENNReal.toReal_one] using hb)
  · intro g
    have hg := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hc) g
    change Tendsto (fun n => NormPreservingLifts.signedFunctional (s n) g)
      (along (historicalJ hCH θ d c))
      (𝓝 (NormPreservingLifts.signedFunctional mu.1 g)) at hg
    simpa only [along, Nat.cofinite_eq_atTop] using hg

/-- Concrete capture data are populated on the very final Prefix diagram.
The actual run remains available with all its Q/R and quantitative G paths. -/
noncomputable def rawHistory : RawHistory (finalPrefix hCH).diagram where
  U := fun b => (wholeBirth hCH b).U
  U_onto := fun b => (wholeBirth hCH b).Uonto
  V := fun b => (wholeBirth hCH b).V
  nu := fun b => (wholeBirth hCH b).nu
  nu_onto := fun b => (wholeBirth hCH b).nuonto
  launch := by
    intro b i
    obtain ⟨a, hba, _, hV⟩ := launch hCH b i b.1
    exact ⟨a, hba, hV⟩
  N₀ := fun b d => reservoir hCH b d false
  N₁ := fun b d => reservoir hCH b d true
  reservoirs_disjoint := reservoirs hCH
  J := historicalJ hCH
  infinite₀ := fun θ d c => infinite hCH θ d c false
  infinite₁ := fun θ d c => infinite hCH θ d c true
  directed := directed hCH
  properF := fun θ d c s hreg hn hm _ => regular_f hCH θ d c s hreg hn hm

end D5.S3.Topology.InverseLimit.SignedOrdinalRawHistory
