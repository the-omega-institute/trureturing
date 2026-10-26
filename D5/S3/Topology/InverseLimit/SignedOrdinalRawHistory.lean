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
    ⟨max θ.1 d, θ.2.trans (le_max_left (ord θ) d.1)⟩).event.result.B _ _

private theorem infinite (θ : Stage) (d : Label) (c : Eligible θ d) (e : Bool) :
    (historicalJ hCH θ d c ∩ reservoir hCH θ d e).Infinite := by
  let C : Stage := ⟨c.1, θ.2.trans ((le_max_left (ord θ) d.1).trans c.2.le)⟩
  let hθ : θ < C := (le_max_left (ord θ) d.1).trans_lt c.2
  let hd : d.1 < ord C := (le_max_right (ord θ) d.1).trans_lt c.2
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
    · let B : Stage := ⟨b.1, θ.2.trans ((le_max_left (ord θ) d.1).trans b.2.le)⟩
      let C : Stage := ⟨c.1, θ.2.trans ((le_max_left (ord θ) d.1).trans c.2.le)⟩
      let hθ : θ < B := (le_max_left (ord θ) d.1).trans_lt b.2
      exact (SignedOrdinalHistory.coherent hCH B C hlt).DJ
        (oldRow hθ (newRow (ord θ) θ.2)) (oldRow_ne hθ _)
        ⟨d.1, (le_max_right (ord θ) d.1).trans_lt b.2⟩
  change (∀ᶠ n in cofinite, n ∈ historicalJ hCH θ d c →
    n ∈ historicalJ hCH θ d b) at hs
  apply (Filter.eventually_cofinite.mp hs).subset
  intro n hn
  exact fun h => hn.2 (h hn.1)

local instance carrierMeasurable {a : Ordinal.{0}} (C : Set (Cube a)) :
    MeasurableSpace C := borel C
local instance carrierBorel {a : Ordinal.{0}} (C : Set (Cube a)) :
    BorelSpace C := ⟨rfl⟩

private theorem current_proper_f (a : Stage) (r : Rows (ord a))
    (hr : r ≠ newRow (ord a) a.2) (d : Coord (ord a))
    {C : Set (Cube (ord a))} {D : Set (Cube r.1)} [CompactSpace C]
    (hC : C = (SignedOrdinalHistory.run hCH a).H.carrier (top (ord a)))
    (hD : D = (SignedOrdinalHistory.run hCH a).H.carrier (rowIndex r))
    (W : BirthPack D)
    (hnu : ∀ n, HEq (W.measure ⟨d.1, (show d.1 < ord a from d.2).trans (show ord a < ω₁ from a.1.2)⟩ n)
      ((((SignedOrdinalHistory.run hCH a).P.nu r hr
        ⟨d.1, (show d.1 < ord a from d.2).trans (show ord a < ω₁ from a.1.2)⟩).1 n).1))
    (f : C(C, D)) (hf : ∀ x, (f x).1 = restrict r.2.2 x.1)
    (s : ℕ → SignedMeasure C)
    (hn : ∀ n, (s n).totalVariation univ = 1)
    (hm : ∀ n, (s n).map f = W.measure ⟨d.1, (show d.1 < ord a from d.2).trans (show ord a < ω₁ from a.1.2)⟩ n) :
    ∃ μ : SignedMeasure C, μ.totalVariation.Regular ∧ μ.totalVariation univ ≤ 1 ∧
      ∀ g : C(C, ℝ), Tendsto (fun n => NormPreservingLifts.signedFunctional (s n) g)
        (cofinite ⊓ 𝓟 ((SignedOrdinalHistory.run hCH a).P.J r hr d))
        (𝓝 (NormPreservingLifts.signedFunctional μ g)) := by
  subst C
  subst D
  have hmap : f = projection (SignedOrdinalHistory.run hCH a).H r := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (hf x)
  apply SignedOrdinalHistory.proper_f hCH a r hr d s ?_ hn
  intro n
  have hm' : (s n).map (projection (SignedOrdinalHistory.run hCH a).H r) =
      W.measure ⟨d.1, (show d.1 < ord a from d.2).trans (show ord a < ω₁ from a.1.2)⟩ n := by
    simpa only [hmap] using hm n
  exact hm'.trans (eq_of_heq (hnu n))

private theorem regular_f (θ : Stage) (d : Label) (c : Eligible θ d)
    (s : ℕ → SignedMeasure ((finalPrefix hCH).Space c.1))
    (_hreg : ∀ n, (s n).totalVariation.Regular)
    (hn : ∀ n, (s n).totalVariation univ = 1)
    (hm : ∀ n, (s n).map
      ((finalPrefix hCH).map θ.1 c.1 ((le_max_left (ord θ) d.1).trans c.2.le)) =
        (((wholeBirth hCH θ).nu d).1 n).1) :
    ∃ μ : SignedMeasure ((finalPrefix hCH).Space c.1), μ.totalVariation.Regular ∧
      μ.totalVariation univ ≤ 1 ∧ ∀ g : C((finalPrefix hCH).Space c.1, ℝ),
        Tendsto (fun n => NormPreservingLifts.signedFunctional (s n) g)
          (cofinite ⊓ 𝓟 (historicalJ hCH θ d c))
          (𝓝 (NormPreservingLifts.signedFunctional μ g)) := by
  let A : Stage := ⟨c.1, θ.2.trans ((le_max_left (ord θ) d.1).trans c.2.le)⟩
  let hθ : θ < A := (le_max_left (ord θ) d.1).trans_lt c.2
  let hd : d.1 < ord A := (le_max_right (ord θ) d.1).trans_lt c.2
  let r := oldRow hθ (newRow (ord θ) θ.2)
  let hr := oldRow_ne hθ (newRow (ord θ) θ.2)
  have hD := carrier_read hCH A (rowIndex r)
  have hp : HEq (wholeBirth hCH θ) ((SignedOrdinalHistory.run hCH A).oldBirth r hr) :=
    (wholeBirth_read hCH θ).trans
      ((heq_of_eq (SignedOrdinalHistory.coherent hCH θ A hθ).birth).trans
        (BirthPack.cast_heq _ _)).symm
  have hnu := fun n => BirthPack.heq_measure hD _ _ hp d n
  exact current_proper_f hCH A r hr ⟨d.1, hd⟩
    (C := (finalPrefix hCH).carrier c.1) (D := (finalPrefix hCH).carrier θ.1)
    (top_read hCH A) hD (wholeBirth hCH θ) hnu
    ((finalPrefix hCH).map θ.1 c.1 hθ.le) (fun _ => rfl) s hn hm

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
