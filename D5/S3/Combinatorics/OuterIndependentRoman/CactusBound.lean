/- GID: D5/S3/Combinatorics/OuterIndependentRoman/CactusBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OuterIndependentRoman/CactusBound
   mirror-E: none(waiver:external-conjecture-resolution)
   anchors: []
   utility: none
   digest: The paired tree labelling and fundamental cycles settle Conjecture 3.3. -/

import D5.S3.Combinatorics.OuterIndependentRoman.CactusLabels
import D5.S3.Combinatorics.OuterIndependentRoman.CactusSupports
import D5.S3.Combinatorics.OuterIndependentRoman.CactusCycles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.OuterIndependentRoman.CactusBound

/-- Conjecture 3.3 of Nazari-Moghaddam, Chellali and Sheikholeslami. -/
theorem result : CactusDefs.claim := by
  classical
  unfold CactusDefs.claim
  intro V _ _ G hG _ hn
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  let col := hT.coloringTwo
  let c : V → Bool := fun v => decide ((col v).val = 0)
  have hc {u v : V} (huv : T.Adj u v) : c u ≠ c v := by
    intro he
    have hne := col.valid huv
    have ha := (col u).isLt
    have hb := (col v).isLt
    have hi : (col u).val = 0 ↔ (col v).val = 0 := decide_eq_decide.mp he
    have heq : (col u).val = (col v).val := by
      by_cases h0 : (col u).val = 0
      · have h1 : (col v).val = 0 := hi.mp h0
        omega
      · have h1 : (col v).val ≠ 0 := fun hv => h0 (hi.mpr hv)
        omega
    exact hne (Fin.ext heq)
  have hpair := CactusLabels.paired_labelling_bound G T hTG c hc
    hT.connected.preconnected.exists_adj_of_nontrivial
  have hs := CactusSupports.support_card_bound T hT.connected hn
  have hcycles := CactusCycles.nonTreeEdges_le_cycles G T hTG hT
  omega

#print axioms result

end D5.S3.Combinatorics.OuterIndependentRoman.CactusBound
