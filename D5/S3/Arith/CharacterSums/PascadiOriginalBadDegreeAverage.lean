/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalBadDegreeAverage
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalBadDegreeAverage
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: Actual long physical charts supply their heights and admit the bad-degree weight average. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalBadDegree
import D5.S3.Arith.CharacterSums.PascadiOriginalWeightAverage

/-! A genuine reduced long basis supplies the coordinate heights. The numerical
cutoffs remain explicit; averaging uses only actual original parameters. -/

open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

/-- The physical long chart supplies every height input of the actual bad-degree
bound. The original numerical separation cutoffs are retained explicitly. -/
theorem actual_long_bad_degree_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (M X Y H : ℝ) (t w : ℤ)
      (B : ReducedMiddleBasis (p^3) t w X Y)
      (B₂ : ReducedMiddleBasis (p^2) t w X Y)
      (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
      (q : Coordinate) (E : Finset Endpoint),
      0 < X → 0 < Y → 2*X < (p^3 : ℕ) → 2*Y < (p^3 : ℕ) →
      0 < H → H^2 = X*Y → (w,t) ∈ literalBox X Y →
      physical B.R B.V q = (-w,-t) →
      ((p^3 : ℕ) : ℝ)^2 < H^2*weightedSq X Y B.R →
      IsUnit (B.R.1 : ZMod (p^3)) →
      IsUnit (t : ZMod (p^3)) → IsUnit (w : ZMod (p^3)) →
      IsUnit (1+a₁*a₂*(t : ZMod (p^3))*(w : ZMod (p^3))) →
      (∀ e ∈ E, WordSolution (p^3) a₁ a₂ B.R B.V q e) →
      (∀ e ∈ E, IsUnit ((physical B.R B.V e.1).1 : ZMod (p^3)) ∧
        IsUnit ((physical B.R B.V e.2).1 : ZMod (p^3))) →
      (∀ e ∈ E, physical B.R B.V e.1 ∈ literalBox X Y ∧
        physical B.R B.V e.2 ∈ literalBox X Y) →
      (32*(X*Y/(p : ℝ)^3))^5 ≤ M^5*(p : ℝ)^3 →
      (10368*(3 : ℝ)^9)^5*M^35 < (p : ℝ)^4 →
      (24*(8*(18 : ℝ))^4)^5*M^40 < (p : ℝ) →
      (actualRecordBadDegree p q B.R B.V E : ℝ) ≤ C*(p : ℝ)^ε*
        (1+6*H/((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R))) := by
  classical
  obtain ⟨C, hC, hdegree⟩ := actual_record_bad_degree_subpower ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp M X Y H t w B B₂ a₁ a₂ ha₁ ha₂ q E hX hY hXsmall hYsmall
    hH hHsq hparameter hq hlong hr ht hw hk hword heunit hebox hcap hlargeR hlargeQ
  have hc : 0 < p^3 := pow_pos hp.pos _
  let σ := Real.sqrt (weightedSq X Y B.R)
  have hQ : 0 < weightedSq X Y B.R := weightedSq_pos hX hY (B.first_ne_zero hc)
  have hσ : 0 < σ := Real.sqrt_pos.mpr hQ
  have hσsq : σ^2 = weightedSq X Y B.R := Real.sq_sqrt hQ.le
  have hσhi : weightedSq X Y B.R < 4*σ^2 := by rw [hσsq]; linarith
  let J₁ := 8*H/σ
  let J₂ := 4*H*σ/(p : ℝ)^3
  obtain ⟨horder, hJ₂, hprod, _⟩ := B.long_scale_bounds hc hX hY H σ
    hH hHsq hσ hσsq.le hσhi hlong
  have horder' : J₂ ≤ J₁ := by simpa only [J₁, J₂, Nat.cast_pow] using horder
  have hJ₂' : 1 ≤ J₂ := by
    have hh : 2 < J₂ := by simpa only [J₂, Nat.cast_pow] using hJ₂
    linarith
  have hprod' : J₁*J₂ = 32*(X*Y/(p : ℝ)^3) := by
    simpa only [J₁, J₂, Nat.cast_pow] using hprod
  have hcoord (z : Coordinate) (hz : physical B.R B.V z ∈ literalBox X Y) :
      CoordinateBound J₁ J₂ z := by
    simpa only [J₁, J₂, Nat.cast_pow] using
      B.coordinate_bound hc hX hY H σ hH hHsq hσ hσsq.le hσhi z hz
  have hqc : CoordinateBound J₁ J₂ q := by
    apply hcoord
    rw [hq]
    exact anchor_mem_literalBox hparameter.1 hparameter.2
  have hEc : ∀ e ∈ E, CoordinateBound J₁ J₂ e.1 ∧ CoordinateBound J₁ J₂ e.2 := by
    intro e he
    exact ⟨hcoord _ (hebox e he).1, hcoord _ (hebox e he).2⟩
  have hk' : IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*
      ((physical B.R B.V q).1 : ZMod (p^3))) := by
    simpa only [hq, ht.unit_spec, Int.cast_neg, mul_neg, sub_neg_eq_add] using hk
  have hcap' : (J₁*J₂)^5 ≤ M^5*(p : ℝ)^3 := by rw [hprod']; exact hcap
  exact hdegree p hp J₁ J₂ M X Y H t w B.toMiddleBasis B₂ a₁ a₂ ha₁ ha₂ q E
    hr ht hw hX hY hXsmall hYsmall hH hHsq hq horder' hJ₂' hk' hqc hEc
    hword heunit hebox hcap' hlargeR hlargeQ

/-- Average the actual bad degrees over the literal original parameter set.
Reduced prime-square bases are selected only on that finite set; no coordinate,
counting, or physical-weight bound is supplied as a hypothesis. -/
theorem actual_long_bad_degree_average (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (M X Y H : ℝ)
      (a₁ a₂ : ZMod (p^3)) (q : Coordinate → Coordinate)
      (RV : Coordinate → Coordinate × Coordinate)
      (s : Finset Coordinate) (E : Coordinate → Finset Endpoint),
      1 ≤ X → X ≤ Y → 2*Y < (p : ℝ)^3 → X*Y < 2*(p : ℝ)^4 →
      0 < H → H^2 = X*Y → (p : ℝ) ≤ H → IsUnit a₁ → IsUnit a₂ →
      (∀ wt ∈ s, wt ∈ literalBox X Y) →
      (∀ wt ∈ s, ∃ B : ReducedMiddleBasis (p^3) wt.2 wt.1 X Y,
        B.R = (RV wt).1 ∧ B.V = (RV wt).2) →
      (∀ wt ∈ s, physical (RV wt).1 (RV wt).2 (q wt) = -wt) →
      (∀ wt ∈ s, (p^3 : ℝ)^2 < (X*Y)*weightedSq X Y (RV wt).1) →
      (∀ wt ∈ s, IsUnit ((RV wt).1.1 : ZMod (p^3))) →
      (∀ wt ∈ s, IsUnit (wt.2 : ZMod (p^3)) ∧ IsUnit (wt.1 : ZMod (p^3))) →
      (∀ wt ∈ s, IsUnit (1+a₁*a₂*(wt.2 : ZMod (p^3))*(wt.1 : ZMod (p^3)))) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        WordSolution (p^3) a₁ a₂ (RV wt).1 (RV wt).2 (q wt) e) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        IsUnit ((physical (RV wt).1 (RV wt).2 e.1).1 : ZMod (p^3)) ∧
        IsUnit ((physical (RV wt).1 (RV wt).2 e.2).1 : ZMod (p^3))) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        physical (RV wt).1 (RV wt).2 e.1 ∈ literalBox X Y ∧
        physical (RV wt).1 (RV wt).2 e.2 ∈ literalBox X Y) →
      (32*(X*Y/(p : ℝ)^3))^5 ≤ M^5*(p : ℝ)^3 →
      (10368*(3 : ℝ)^9)^5*M^35 < (p : ℝ)^4 →
      (24*(8*(18 : ℝ))^4)^5*M^40 < (p : ℝ) →
      (∑ wt ∈ s, (actualRecordBadDegree p (q wt) (RV wt).1 (RV wt).2 (E wt) : ℝ)) ≤
        C*(p : ℝ)^ε*(X*Y+(X*Y/p)*(1+Real.log (2*p)/Real.log 2)+
          (X*Y)^2/(p : ℝ)^4) := by
  classical
  obtain ⟨C, hC, hdegree⟩ := actual_long_bad_degree_subpower ε hε
  refine ⟨12288*C, by positivity, ?_⟩
  intro p hp M X Y H a₁ a₂ q RV s E hX1 hXY hYsmall hAcut hH hHsq hHp ha₁ ha₂
    hsbox hred hanchor hlong hr hunit hrhs hword heunit hebox hcap hlargeR hlargeQ
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hY : 0 < Y := hX.trans_le hXY
  have hp2 : 0 < p^2 := pow_pos hp.pos _
  letI : NeZero (p^2) := ⟨hp2.ne'⟩
  let f : ZMod (p^3) →+* ZMod (p^2) :=
    ZMod.castHom (pow_dvd_pow p (by decide : 2 ≤ 3)) (ZMod (p^2))
  have hunit₂ (wt : Coordinate) (hw : wt ∈ s) :
      IsUnit (wt.2 : ZMod (p^2)) ∧ IsUnit (wt.1 : ZMod (p^2)) :=
    ⟨by simpa only [map_intCast] using (hunit wt hw).1.map f,
      by simpa only [map_intCast] using (hunit wt hw).2.map f⟩
  have hex (wt : Coordinate) (hw : wt ∈ s) :
      Nonempty (ReducedMiddleBasis (p^2) wt.2 wt.1 X Y) :=
    exists_reduced_middle_basis (p^2) wt.2 wt.1 X Y hp2 hX hY (hunit₂ wt hw).2
  let U := fun wt => if hw : wt ∈ s then (Classical.choice (hex wt hw)).R else 0
  have hB₂ (wt : Coordinate) (hw : wt ∈ s) :
      ∃ B₂ : ReducedMiddleBasis (p^2) wt.2 wt.1 X Y, U wt = B₂.R :=
    ⟨Classical.choice (hex wt hw), dif_pos hw⟩
  have hYcut : Y < (p : ℝ)^3 := by linarith
  have hYcube : 2*Y < (p^3 : ℕ) := by exact_mod_cast hYsmall
  have hXcube : 2*X < (p^3 : ℕ) := (by linarith : 2*X ≤ 2*Y).trans_lt hYcube
  let W := fun wt => 1+H/((p : ℝ)*Real.sqrt (weightedSq X Y (U wt)))
  have hD (wt : Coordinate) (hw : wt ∈ s) :
      (actualRecordBadDegree p (q wt) (RV wt).1 (RV wt).2 (E wt) : ℝ) ≤
        (6*C)*(p : ℝ)^ε*W wt := by
    obtain ⟨B, hBR, hBV⟩ := hred wt hw
    obtain ⟨B₂, hBU⟩ := hB₂ wt hw
    have hq : physical B.R B.V (q wt) = (-wt.1,-wt.2) := by
      rw [hBR, hBV]
      exact (hanchor wt hw).trans (Prod.ext (Prod.fst_neg wt) (Prod.snd_neg wt))
    have hlongB : ((p^3 : ℕ) : ℝ)^2 < H^2*weightedSq X Y B.R := by
      rw [hHsq, hBR]
      simpa only [Nat.cast_pow] using hlong wt hw
    have hd := hdegree p hp M X Y H wt.2 wt.1 B B₂ a₁ a₂ ha₁ ha₂ (q wt) (E wt)
      hX hY hXcube hYcube hH hHsq (hsbox wt hw) hq hlongB
      (by simpa only [hBR] using hr wt hw) (hunit wt hw).1 (hunit wt hw).2 (hrhs wt hw)
      (by simpa only [hBR, hBV] using hword wt hw)
      (by simpa only [hBR, hBV] using heunit wt hw)
      (by simpa only [hBR, hBV] using hebox wt hw) hcap hlargeR hlargeQ
    have hd' : (actualRecordBadDegree p (q wt) (RV wt).1 (RV wt).2 (E wt) : ℝ) ≤
        C*(p : ℝ)^ε*(1+6*H/((p : ℝ)*Real.sqrt (weightedSq X Y (U wt)))) := by
      simpa only [hBR, hBV, ← hBU] using hd
    have hwscale : 1+6*H/((p : ℝ)*Real.sqrt (weightedSq X Y (U wt))) ≤ 6*W wt := by
      dsimp only [W]
      simp only [mul_div_assoc]
      linarith
    calc
      _ ≤ C*(p : ℝ)^ε*(1+6*H/((p : ℝ)*Real.sqrt (weightedSq X Y (U wt)))) := hd'
      _ ≤ C*(p : ℝ)^ε*(6*W wt) := mul_le_mul_of_nonneg_left hwscale (by positivity)
      _ = _ := by ring
  have hweight := actual_physical_weight_average hp hX1 hXY hYcut hAcut hH hHsq hHp
    s hsbox hunit₂ U hB₂
  change (∑ wt ∈ s, W wt) ≤ _ at hweight
  calc
    _ ≤ ∑ wt ∈ s, (6*C)*(p : ℝ)^ε*W wt := Finset.sum_le_sum hD
    _ = ((6*C)*(p : ℝ)^ε)*(∑ wt ∈ s, W wt) := (Finset.mul_sum _ _ _).symm
    _ ≤ ((6*C)*(p : ℝ)^ε)*(2048*(X*Y+(X*Y/p)*(1+Real.log (2*p)/Real.log 2)+
        (X*Y)^2/(p : ℝ)^4)) := mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = _ := by ring

end
end D5.S3.Arith.CharacterSums.Original
