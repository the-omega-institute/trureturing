/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalBadDegree
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalBadDegree
   mirror-E: none(waiver:open-total-original-count)
   anchors: []
   utility: none
   digest: The actual maximum bad-partner degree has a weighted subpower bound. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalDerivativePartners
import D5.S3.Arith.CharacterSums.PascadiOriginalGoodRecordMoment

/-! Select an actual retained baseline attaining the finite maximum. The empty
chart has degree zero; every nonempty chart consumes the actual partner bound. -/

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

/-- The actual maximum derivative-zero degree obeys the uniform weighted bound.
All retained baselines are included, with the same original parameters and
units; no estimate for a counting or injection supplier is assumed. -/
theorem actual_record_bad_degree_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (J₁ J₂ M X Y H : ℝ) (t w : ℤ)
      (B : MiddleBasis (p^3) t w) (B₂ : ReducedMiddleBasis (p^2) t w X Y)
      (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
      (q : Coordinate) (E : Finset Endpoint)
      (hr : IsUnit (B.R.1 : ZMod (p^3)))
      (ht : IsUnit (t : ZMod (p^3))) (hw : IsUnit (w : ZMod (p^3))),
      0 < X → 0 < Y → 2*X < (p^3 : ℕ) → 2*Y < (p^3 : ℕ) →
      0 < H → H^2 = X*Y → physical B.R B.V q = (-w, -t) →
      J₂ ≤ J₁ → 1 ≤ J₂ →
      IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*((physical B.R B.V q).1 : ZMod (p^3))) →
      CoordinateBound J₁ J₂ q →
      (∀ e ∈ E, CoordinateBound J₁ J₂ e.1 ∧ CoordinateBound J₁ J₂ e.2) →
      (∀ e ∈ E, WordSolution (p^3) a₁ a₂ B.R B.V q e) →
      (∀ e ∈ E, IsUnit ((physical B.R B.V e.1).1 : ZMod (p^3)) ∧
        IsUnit ((physical B.R B.V e.2).1 : ZMod (p^3))) →
      (∀ e ∈ E, physical B.R B.V e.1 ∈ literalBox X Y ∧
        physical B.R B.V e.2 ∈ literalBox X Y) →
      (J₁*J₂)^5 ≤ M^5*(p : ℝ)^3 →
      (10368*(3 : ℝ)^9)^5*M^35 < (p : ℝ)^4 →
      (24*(8*(18 : ℝ))^4)^5*M^40 < (p : ℝ) →
      (actualRecordBadDegree p q B.R B.V E : ℝ) ≤ C*(p : ℝ)^ε*
        (1+6*H/((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R))) := by
  classical
  obtain ⟨C, hC, hcount⟩ := actual_derivative_zero_partners_subpower ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp J₁ J₂ M X Y H t w B B₂ a₁ a₂ ha₁ ha₂ q E hr ht hw
    hX hY hXsmall hYsmall hH hHsq hq h₁₂ h₂ hk hqc hE hword hunit hbox
    hcap hlargeR hlargeQ
  by_cases hne : E.Nonempty
  · obtain ⟨base, hb, hmax⟩ := Finset.exists_mem_eq_sup E hne
      (fun base => (actualRecordBadPartners p q B.R B.V E base).card)
    change (((E.sup fun base =>
      (actualRecordBadPartners p q B.R B.V E base).card) : ℕ) : ℝ) ≤ _
    rw [hmax]
    let S := actualRecordBadPartners p q B.R B.V E base
    have hmem (e : Endpoint) (he : e ∈ S) : e ∈ E := (Finset.mem_filter.mp he).1
    apply hcount p hp J₁ J₂ M X Y H t w B B₂ a₁ a₂ ha₁ ha₂ q base S hr ht hw
      hX hY hXsmall hYsmall hH hHsq hq h₁₂ h₂ (hword base hb)
      (hunit base hb).1 (hunit base hb).2 hk hqc (hE base hb).1 (hE base hb).2
      (fun e he => hE e (hmem e he)) (fun e he => hword e (hmem e he))
      (fun e he => hbox e (hmem e he)) ?_ hcap hlargeR hlargeQ
    intro e he
    have hd := (Finset.mem_filter.mp he).2
    have hinv : (↑hr.unit⁻¹ : ZMod (p^3)) = (B.R.1 : ZMod (p^3))⁻¹ := by
      rw [← ZMod.inv_coe_unit, hr.unit_spec]
    simpa only [recordBeta, hinv] using hd
  · have hEzero : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hdegree : actualRecordBadDegree p q B.R B.V ∅ = 0 := by
      simp [actualRecordBadDegree]
    rw [hEzero, hdegree, Nat.cast_zero]
    positivity

end
end D5.S3.Arith.CharacterSums.Original
