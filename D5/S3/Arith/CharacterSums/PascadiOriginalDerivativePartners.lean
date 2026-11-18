/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalDerivativePartners
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalDerivativePartners
   mirror-E: none(waiver:open-total-original-count)
   anchors: []
   utility: none
   digest: Every actual derivative-zero partner stratum has one uniform physical-weight bound. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalAlignedPartners
import D5.S3.Arith.CharacterSums.PascadiOriginalSingularCount

/-! The literal derivative-zero partners split into zero and nonzero reductions.
Both counts retain the original word, baseline and units, including aligned baselines. -/

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

/-- All actual derivative-zero partners satisfy the uniform subpower estimate.
The exceptional zero-reduction stratum and genuine nonzero singular stratum
are both included, and the physical linear-fiber weight is paid only once. -/
theorem actual_derivative_zero_partners_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (J₁ J₂ M X Y H : ℝ) (t w : ℤ)
      (B : MiddleBasis (p^3) t w) (B₂ : ReducedMiddleBasis (p^2) t w X Y)
      (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
      (q : Coordinate) (base : Endpoint) (S : Finset Endpoint)
      (hr : IsUnit (B.R.1 : ZMod (p^3)))
      (ht : IsUnit (t : ZMod (p^3))) (hw : IsUnit (w : ZMod (p^3))),
      0 < X → 0 < Y → 2*X < (p^3 : ℕ) → 2*Y < (p^3 : ℕ) →
      0 < H → H^2 = X*Y → physical B.R B.V q = (-w, -t) →
      J₂ ≤ J₁ → 1 ≤ J₂ →
      WordSolution (p^3) a₁ a₂ B.R B.V q base →
      IsUnit ((physical B.R B.V base.1).1 : ZMod (p^3)) →
      IsUnit ((physical B.R B.V base.2).1 : ZMod (p^3)) →
      IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*((physical B.R B.V q).1 : ZMod (p^3))) →
      CoordinateBound J₁ J₂ q → CoordinateBound J₁ J₂ base.1 → CoordinateBound J₁ J₂ base.2 →
      (∀ e ∈ S, CoordinateBound J₁ J₂ e.1 ∧ CoordinateBound J₁ J₂ e.2) →
      (∀ e ∈ S, WordSolution (p^3) a₁ a₂ B.R B.V q e) →
      (∀ e ∈ S, physical B.R B.V e.1 ∈ literalBox X Y ∧
        physical B.R B.V e.2 ∈ literalBox X Y) →
      (∀ e ∈ S, (pencil q base e).derivative.eval₂ (Int.castRingHom (ZMod p))
        ((ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p))
          ((B.V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3)))) = 0) →
      (J₁*J₂)^5 ≤ M^5*(p : ℝ)^3 →
      (10368*(3 : ℝ)^9)^5*M^35 < (p : ℝ)^4 →
      (24*(8*(18 : ℝ))^4)^5*M^40 < (p : ℝ) →
      (S.card : ℝ) ≤ C*(p : ℝ)^ε*
        (1+6*H/((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R))) := by
  classical
  obtain ⟨C₀, hC₀, hzero⟩ := actual_zero_reduction_partners_subpower ε hε
  obtain ⟨C₁, hC₁, hnonzero⟩ := actual_nonzero_singular_partners_subpower ε hε
  refine ⟨C₀+C₁, by positivity, ?_⟩
  intro p hp J₁ J₂ M X Y H t w B B₂ a₁ a₂ ha₁ ha₂ q base S hr ht hw
    hX hY hXsmall hYsmall hH hHsq hq h₁₂ h₂ hbase hx hy hk
    hqc hb₁ hb₂ hS hword hbox hderiv hcap hlargeR hlargeQ
  let Z := fun e : Endpoint => (pencil q base e).map (Int.castRingHom (ZMod p)) = 0
  let S₀ := S.filter Z
  let S₁ := S.filter fun e => ¬ Z e
  have hrestrict₀ {P : Endpoint → Prop} (h : ∀ e ∈ S, P e) : ∀ e ∈ S₀, P e :=
    fun e he => h e (Finset.mem_filter.mp he).1
  have hrestrict₁ {P : Endpoint → Prop} (h : ∀ e ∈ S, P e) : ∀ e ∈ S₁, P e :=
    fun e he => h e (Finset.mem_filter.mp he).1
  have htu : IsUnit (-(physical B.R B.V q).2 : ZMod (p^3)) := by
    simpa only [hq, Int.cast_neg, neg_neg] using ht
  have htuval : (htu.unit : ZMod (p^3)) = t := by
    rw [htu.unit_spec]
    simp only [hq, Int.cast_neg, neg_neg]
  have hk' : IsUnit (1-a₁*a₂*(htu.unit : ZMod (p^3))*
      ((physical B.R B.V q).1 : ZMod (p^3))) := by
    simpa only [htuval, ht.unit_spec] using hk
  have h₀ : (S₀.card : ℝ) ≤ C₀*(p : ℝ)^ε :=
    hzero p hp J₁ J₂ M X Y t w B a₁ a₂ ha₁ ha₂ q base S₀ hr htu hw
      hq hXsmall hYsmall h₁₂ h₂ hbase hx hy hk' hqc hb₁ hb₂
      (hrestrict₀ hS) (hrestrict₀ hword) (hrestrict₀ hbox)
      (fun _ he => (Finset.mem_filter.mp he).2) hcap hlargeQ
  have h₁ : (S₁.card : ℝ) ≤ C₁*(p : ℝ)^ε*
      (1+6*H/((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R))) :=
    hnonzero p hp J₁ J₂ M X Y H t w B B₂ a₁ a₂ ha₁ ha₂ q base S₁ hr ht hw
      hX hY hXsmall hYsmall hH hHsq hq h₁₂ h₂ hbase hx hy hk hqc hb₁ hb₂
      (hrestrict₁ hS) (hrestrict₁ hword) (hrestrict₁ hbox)
      (fun _ he => (Finset.mem_filter.mp he).2) (hrestrict₁ hderiv) hcap hlargeR hlargeQ
  let W : ℝ := 1+6*H/((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R))
  have hW : 1 ≤ W := by
    have hh : 0 ≤ 6*H/((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R)) := by positivity
    dsimp only [W]
    linarith
  have hcard : (S.card : ℝ) = (S₀.card : ℝ)+(S₁.card : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := S) Z).symm
  calc
    (S.card : ℝ) = (S₀.card : ℝ)+(S₁.card : ℝ) := hcard
    _ ≤ C₀*(p : ℝ)^ε+C₁*(p : ℝ)^ε*W := add_le_add h₀ h₁
    _ ≤ C₀*(p : ℝ)^ε*W+C₁*(p : ℝ)^ε*W := add_le_add
      (show C₀*(p : ℝ)^ε ≤ C₀*(p : ℝ)^ε*W from
        le_mul_of_one_le_right (by positivity) hW) le_rfl
    _ = (C₀+C₁)*(p : ℝ)^ε*W := by ring

end
end D5.S3.Arith.CharacterSums.Original
