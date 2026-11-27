import D5.S3.Quantum.Semigroups.WuCubicHotOuter

/-! Exact rational replay of the outer spectral subdivision. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Matrix
open Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicHotOuterFinite

open WuCubicHotOuter
open WuCubicDirectedOccupationCap (Mat)
open WuCubicAngularCertificate (normalizedDeficit)
open WuCubicSpectralVariance (alphaLossFactor boxVarianceUpper spectralCutCap thermalEntropyPenalty)

private structure Box where
  aLo : ℚ
  aHi : ℚ
  cLo : ℚ
  cHi : ℚ
  sLo : ℚ
  sHi : ℚ

private noncomputable def Box.toReal (B : Box) : ShapeBox :=
  ⟨B.aLo, B.aHi, B.cLo, B.cHi, B.sLo, B.sHi⟩

private def Box.root (height : ℚ) : Box :=
  ⟨0, 1, 0, 1, height / ((3/4)*(1+height)), 1⟩

private theorem Box.root_cast (height : ℚ) :
    (Box.root height).toReal = ShapeBox.root (height : ℝ) := by
  simp [Box.root, Box.toReal, ShapeBox.root, spreadFloor]

private def Box.bisect (B : Box) (axis : Fin 3) : Box × Box :=
  ![({ B with aHi := (B.aLo+B.aHi)/2 }, { B with aLo := (B.aLo+B.aHi)/2 }),
    ({ B with cHi := (B.cLo+B.cHi)/2 }, { B with cLo := (B.cLo+B.cHi)/2 }),
    ({ B with sHi := (B.sLo+B.sHi)/2 }, { B with sLo := (B.sLo+B.sHi)/2 })] axis

private theorem Box.bisect_cast (B : Box) (axis : Fin 3) :
    ((B.bisect axis).1.toReal, (B.bisect axis).2.toReal) = B.toReal.bisect axis := by
  fin_cases axis <;> simp [Box.bisect, Box.toReal, ShapeBox.bisect]

private def Box.aUpper (B : Box) : ℚ := min B.aHi (1-B.cLo)
private def Box.cUpper (B : Box) : ℚ := min B.cHi (1-B.aLo)

private def denominator (height f : ℚ) : ℚ := max f (1-f) + f*height

private def Box.sLower (B : Box) (height : ℚ) : ℚ :=
  let flo := (2-B.aUpper+B.cLo)/4
  let fhi := (2-B.aLo+B.cUpper)/4
  max B.sLo (height / max (denominator height flo) (denominator height fhi))

private theorem Box.sLower_cast (B : Box) (height : ℚ) :
    (B.sLower height : ℝ) = B.toReal.sLower height := by
  simp [Box.sLower, Box.aUpper, Box.cUpper, denominator, Box.toReal,
    ShapeBox.sLower, ShapeBox.aUpper, ShapeBox.cUpper, shapeDenominator]

private def Box.lowerRoots (B : Box) : Fin 4 → ℚ :=
  ![1-B.sHi, 1-(1-B.aLo)*B.sHi, 1-B.cUpper*B.sHi, 1]

private def Box.upperRoots (B : Box) (height : ℚ) : Fin 4 → ℚ :=
  ![1-B.sLower height, 1-(1-B.aUpper)*B.sLower height, 1-B.cLo*B.sLower height, 1]

private def Box.lowerGaps (B : Box) : Fin 3 → ℚ :=
  ![B.aLo, max 0 (1-B.aUpper-B.cUpper), B.cLo]

private def Box.upperGaps (B : Box) : Fin 3 → ℚ :=
  ![B.aUpper, 1-B.aLo-B.cLo, B.cUpper]

private theorem Box.lowerRoots_cast (B : Box) :
    (fun i => (B.lowerRoots i : ℝ)) = B.toReal.lowerRoots := by
  funext i
  fin_cases i <;> simp [Box.lowerRoots, Box.cUpper, Box.toReal,
    ShapeBox.lowerRoots, ShapeBox.cUpper]

private theorem Box.upperRoots_cast (B : Box) (height : ℚ) :
    (fun i => (B.upperRoots height i : ℝ)) = B.toReal.upperRoots height := by
  funext i
  fin_cases i <;> simp [Box.upperRoots, Box.aUpper, B.sLower_cast, Box.toReal,
    ShapeBox.upperRoots, ShapeBox.aUpper]

private theorem Box.lowerGaps_cast (B : Box) :
    (fun i => (B.lowerGaps i : ℝ)) = B.toReal.lowerGaps := by
  funext i
  fin_cases i <;> simp [Box.lowerGaps, Box.aUpper, Box.cUpper, Box.toReal,
    ShapeBox.lowerGaps, ShapeBox.aUpper, ShapeBox.cUpper]

private theorem Box.upperGaps_cast (B : Box) :
    (fun i => (B.upperGaps i : ℝ)) = B.toReal.upperGaps := by
  funext i
  fin_cases i <;> simp [Box.upperGaps, Box.aUpper, Box.cUpper, Box.toReal,
    ShapeBox.upperGaps, ShapeBox.aUpper, ShapeBox.cUpper]

private def ratMass (x : Fin 4 → ℚ) : ℚ :=
  x 0^3 + x 1^3 + x 2^3 + x 3^3

private def ratEdge (slo shi llo lhi ulo uhi : ℚ) : ℚ :=
  let k := if ulo = 0 then 1 else min 1 (shi*lhi/ulo)
  let gamma := 9/4 * ((3/4)/(1+2*k^2/3) + (1/4)/(1+2*k^2)) - 3/8 - k^2/25
  slo^2*llo^4*gamma/(4*uhi)

private theorem ratEdge_cast (slo shi llo lhi ulo uhi : ℚ) :
    (ratEdge slo shi llo lhi ulo uhi : ℝ) = edgeBoxFloor slo shi llo lhi ulo uhi := by
  by_cases hz : ulo = 0
  · have hr : (ulo : ℝ) = 0 := by exact_mod_cast hz
    simp [ratEdge, edgeBoxFloor, edgeGamma, hz, hr]
  · have hr : (ulo : ℝ) ≠ 0 := by exact_mod_cast hz
    simp [ratEdge, edgeBoxFloor, edgeGamma, hz, hr]

private def ratTracial (T slo shi : ℚ) (lower upper : Fin 4 → ℚ)
    (zlo zhi : Fin 3 → ℚ) : ℚ :=
  let dlo := lower 0^3 - (upper 1*upper 2)^3
  let dhi := upper 0^3 - (lower 1*lower 2)^3
  let det := 4 * (max 0 (max dlo (-dhi)))^2 / (shi^2 * ratMass upper^3)
  (ratEdge slo shi (zlo 0) (zhi 0) (lower 0+lower 1) (upper 0+upper 1) +
    ratEdge slo shi (1-zhi 2) (1-zlo 2) (lower 0+lower 2) (upper 0+upper 2) +
    ratEdge slo shi (1-zhi 0) (1-zlo 0) (lower 1+lower 3) (upper 1+upper 3) +
    ratEdge slo shi (zlo 2) (zhi 2) (lower 2+lower 3) (upper 2+upper 3) + det)/(1+T^2)

private theorem ratTracial_cast (T slo shi : ℚ) (lower upper : Fin 4 → ℚ)
    (zlo zhi : Fin 3 → ℚ) :
    (ratTracial T slo shi lower upper zlo zhi : ℝ) =
      tracialBoxFloor T slo shi (fun i => lower i) (fun i => upper i)
        (fun i => zlo i) (fun i => zhi i) := by
  simp [ratTracial, ratEdge_cast, determinantBoxFloor, tracialBoxFloor,
    ratMass, mass, Fin.sum_univ_four]

private def ratVariance (lower upper : Fin 4 → ℚ) : ℚ :=
  ((upper 1^3-lower 0^3)^2 + (upper 2^3-lower 0^3)^2 + (upper 3^3-lower 0^3)^2 +
    (upper 2^3-lower 1^3)^2 + (upper 3^3-lower 1^3)^2 +
    (upper 3^3-lower 2^3)^2) / ratMass lower^2

private theorem ratVariance_cast (lower upper : Fin 4 → ℚ) :
    (ratVariance lower upper : ℝ) =
      boxVarianceUpper (fun i => (lower i : ℝ)^3) (fun i => (upper i : ℝ)^3) := by
  simp (config := {decide := true}) [ratVariance, ratMass, boxVarianceUpper, Finset.sum_filter,
    Fin.sum_univ_four, add_assoc] <;> ring

private def ratHeat (T loss shi : ℚ) (lower upper : Fin 4 → ℚ) : ℚ :=
  let w := T/(2+T)
  let alphaLoss := (1-w^2)/((2+T)^2*(3+w^2))
  let penalty := max 0 (1/(2*(1+0+(0 : ℚ)^2))-alphaLoss)
  let base := 9/(4*(1+T+T^2))-9/8
  let uniform := base-(7/5)*loss
  let variance := base-min (7/5) (ratVariance lower upper)*penalty
  max uniform variance * ratMass lower / shi^2

private theorem ratHeat_cast (T loss shi : ℚ) (lower upper : Fin 4 → ℚ) :
    (ratHeat T loss shi lower upper : ℝ) =
      heatBox T loss shi (fun i => lower i) (fun i => upper i) := by
  simp [ratHeat, ratVariance_cast, heatBox, cellCoefficient, uniformCoefficient,
    varianceCoefficient, thermalEntropyPenalty, alphaLossFactor, ratMass, mass, Fin.sum_univ_four]

private def ratMinimum (w p : ℚ) : ℚ :=
  if 2*w ≤ p then w-p else -p^2/(4*w)

private theorem ratMinimum_cast (w p : ℚ) :
    (ratMinimum w p : ℝ) = chargeMinimum w p := by
  have hc : (2 : ℝ) * (w : ℝ) ≤ (p : ℝ) ↔ (2 : ℚ)*w ≤ p := by
    simpa only [Rat.cast_mul, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ) (p := 2*w) (q := p))
  unfold ratMinimum chargeMinimum
  by_cases h : (2 : ℚ) * w ≤ p
  · rw [if_pos h, if_pos (hc.mpr h), Rat.cast_sub]
  · rw [if_neg h, if_neg (mt hc.mp h)]
    push_cast
    rfl

private def ratCell (v d0 d1 d2 l u : ℚ) (p : Fin 3 → ℚ) (j H t : ℚ) : ℚ :=
  v + (d0-t*p 0+ratMinimum (d0+l) (t*p 0))/2 + ratMinimum d1 (t*p 1) +
    (d2-t*p 2+ratMinimum (d2+u) (t*p 2))/2 - j*t + H*t^2

private theorem ratCell_cast (v d0 d1 d2 l u : ℚ) (p : Fin 3 → ℚ) (j H t : ℚ) :
    (ratCell v d0 d1 d2 l u p j H t : ℝ) = cellValue v d0 d1 d2 l u (fun i => p i) j H t := by
  simp [ratCell, cellValue, ratMinimum_cast]

private def ratDiagonal (T : ℚ) (lower : Fin 4 → ℚ) (zlo : Fin 3 → ℚ) (i : Fin 3) : ℚ :=
  (9/8/(1+T^2))*zlo i^2*(lower i.castSucc+lower i.succ)

private def ratAdjacent (T : ℚ) (lower : Fin 4 → ℚ) (zlo : Fin 3 → ℚ) (i j : Fin 3) : ℚ :=
  (9/8/(1+T^2))*zlo i*zlo j*((lower i.castSucc+lower i.succ)+(lower j.castSucc+lower j.succ))

private def ratCharge (slo shi : ℚ) (upper : Fin 4 → ℚ) (zhi : Fin 3 → ℚ) (i : Fin 3) : ℚ :=
  let a := upper i.castSucc
  let b := upper i.succ
  (3/2)*zhi i*(a^2+a*b+b^2)/slo+(3/16)*shi*zhi i*(1+zhi i^2)

private def ratSkew (shi : ℚ) (zlo zhi : Fin 3 → ℚ) : ℚ :=
  (3/16)*shi*(zhi 0*(1-zlo 0^2) + 2*zhi 1*(1-zlo 1^2) + zhi 2*(1-zlo 2^2))

private theorem ratDiagonal_cast (T : ℚ) (lower : Fin 4 → ℚ) (zlo : Fin 3 → ℚ) (i : Fin 3) :
    (ratDiagonal T lower zlo i : ℝ) = diagonalBox T (fun k => lower k) (fun k => zlo k) i := by
  simp [ratDiagonal, diagonalBox, adjacentSum]

private theorem ratAdjacent_cast (T : ℚ) (lower : Fin 4 → ℚ) (zlo : Fin 3 → ℚ) (i j : Fin 3) :
    (ratAdjacent T lower zlo i j : ℝ) =
      adjacentBox T (fun k => lower k) (fun k => zlo k) i j := by
  simp [ratAdjacent, adjacentBox, adjacentSum]

private theorem ratCharge_cast (slo shi : ℚ) (upper : Fin 4 → ℚ) (zhi : Fin 3 → ℚ) :
    (fun i => (ratCharge slo shi upper zhi i : ℝ)) =
      chargeBox slo shi (fun k => upper k) (fun k => zhi k) := by
  funext i
  simp [ratCharge, chargeBox]

private theorem ratSkew_cast (shi : ℚ) (zlo zhi : Fin 3 → ℚ) :
    (ratSkew shi zlo zhi : ℝ) = skewBox shi (fun k => zlo k) (fun k => zhi k) := by
  simp [ratSkew, skewBox, spectralCutCap, Fin.sum_univ_three, add_assoc]

private def Box.bound (B : Box) (T height loss : ℚ) : ℚ :=
  let lower := B.lowerRoots
  let upper := B.upperRoots height
  let slo := B.sLower height
  let zlo := B.lowerGaps
  let zhi := B.upperGaps
  let d := ratDiagonal T lower zlo
  let v := ratTracial T slo B.sHi lower upper zlo zhi
  let l := ratAdjacent T lower zlo 0 1
  let u := ratAdjacent T lower zlo 1 2
  let p := ratCharge slo B.sHi upper zhi
  let j := ratSkew B.sHi zlo zhi
  let H := ratHeat T loss B.sHi lower upper
  let base := ratCell v (d 0) (d 1) (d 2) l u p j 0 0
  let penalty := base - ratCell v (d 0) (d 1) (d 2) l u p j 0 T
  base + ratMinimum (H*T^2) penalty

private theorem Box.bound_cast (B : Box) (T height loss : ℚ) :
    (B.bound T height loss : ℝ) = B.toReal.bound T height loss := by
  simp only [Box.bound, ShapeBox.bound, secantFloor, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_zero, ratMinimum_cast, ratCell_cast, ratHeat_cast, ratTracial_cast,
    ratDiagonal_cast, ratAdjacent_cast, ratCharge_cast, ratSkew_cast,
    B.sLower_cast, B.lowerRoots_cast, B.upperRoots_cast, B.lowerGaps_cast, B.upperGaps_cast]
  all_goals rfl

private structure Parameters where
  margin : ℚ
  limit : ℚ
  height : ℚ
  loss : ℚ

private inductive Tree where
  | leaf
  | prune
  | split (axis : Fin 3) (left right : Tree)

private def endpoints (B : Box) : Prop :=
  0 ≤ B.aLo ∧ 0 ≤ B.cLo ∧ 0 < B.sLo ∧ B.sHi ≤ 1

private instance instDecidableEndpoints (B : Box) : Decidable (endpoints B) := by
  unfold endpoints
  infer_instance

private def Tree.check (P : Parameters) : Tree → Box → Bool
  | .leaf, B => decide (endpoints B ∧ P.margin < B.bound P.limit P.height P.loss)
  | .prune, B => decide (endpoints B ∧ (1 < B.aLo+B.cLo ∨ B.sHi < B.sLower P.height))
  | .split axis left right, B =>
      left.check P (B.bisect axis).1 && right.check P (B.bisect axis).2

private abbrev Test (P : Parameters) (B : Box) : Prop :=
  HotBoxTest (P.margin : ℝ) (P.limit : ℝ) (P.height : ℝ) (P.loss : ℝ) B.toReal

private theorem endpoints_cast {B : Box} (h : endpoints B) :
    0 ≤ B.toReal.aLo ∧ 0 ≤ B.toReal.cLo ∧ 0 < B.toReal.sLo ∧ B.toReal.sHi ≤ 1 := by
  obtain ⟨ha, hc, hs, ht⟩ := h
  change 0 ≤ (B.aLo : ℝ) ∧ 0 ≤ (B.cLo : ℝ) ∧ 0 < (B.sLo : ℝ) ∧ (B.sHi : ℝ) ≤ 1
  exact ⟨by exact_mod_cast ha, by exact_mod_cast hc, by exact_mod_cast hs, by exact_mod_cast ht⟩

private theorem split_test {P : Parameters} {B : Box} (axis : Fin 3)
    (left : Test P (B.bisect axis).1) (right : Test P (B.bisect axis).2) : Test P B := by
  have hl := congrArg Prod.fst (B.bisect_cast axis)
  have hr := congrArg Prod.snd (B.bisect_cast axis)
  change ((B.bisect axis).1).toReal = (B.toReal.bisect axis).1 at hl
  change ((B.bisect axis).2).toReal = (B.toReal.bisect axis).2 at hr
  change HotBoxTest _ _ _ _ ((B.bisect axis).1).toReal at left
  change HotBoxTest _ _ _ _ ((B.bisect axis).2).toReal at right
  rw [hl] at left
  rw [hr] at right
  exact HotBoxTest.split axis left right

private theorem Tree.sound (P : Parameters) (tree : Tree) (B : Box)
    (h : tree.check P B = true) : Test P B := by
  induction tree generalizing B with
  | leaf =>
      have h' : endpoints B ∧ P.margin < B.bound P.limit P.height P.loss :=
        of_decide_eq_true h
      obtain ⟨ha, hc, hs, ht⟩ := endpoints_cast h'.1
      apply HotBoxTest.leaf ha hc hs ht
      rw [← B.bound_cast]
      exact Rat.cast_lt.mpr h'.2
  | prune =>
      have h' : endpoints B ∧ (1 < B.aLo+B.cLo ∨ B.sHi < B.sLower P.height) :=
        of_decide_eq_true h
      obtain ⟨ha, hc, hs, ht⟩ := endpoints_cast h'.1
      apply HotBoxTest.prune ha hc hs ht
      rcases h'.2 with hsum | hslo
      · left
        change 1 < (B.aLo : ℝ)+(B.cLo : ℝ)
        exact_mod_cast hsum
      · right
        rw [← B.sLower_cast]
        exact Rat.cast_lt.mpr hslo
  | split axis left right ihl ihr =>
      have hand : (left.check P (B.bisect axis).1 && right.check P (B.bisect axis).2) = true := h
      obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp hand
      exact split_test axis (ihl _ hl) (ihr _ hr)

-- BEGIN GENERATED CERTIFICATES

private def extendedParameters : Parameters := ⟨1/4000, 105241/2125200, 1209149759/5236664020, 3/7⟩

private def extendedBox : Box := Box.root extendedParameters.height

private def extendedBoxL : Box := (extendedBox.bisect 0).1

private def extendedBoxR : Box := (extendedBox.bisect 0).2

private def extendedBoxLL : Box := (extendedBoxL.bisect 1).1

private def extendedBoxLR : Box := (extendedBoxL.bisect 1).2

private def extendedBoxLLL : Box := (extendedBoxLL.bisect 2).1

private def extendedBoxLLR : Box := (extendedBoxLL.bisect 2).2

private def extendedBoxLLLL : Box := (extendedBoxLLL.bisect 0).1

private def extendedBoxLLLR : Box := (extendedBoxLLL.bisect 0).2

private def extendedBoxLLLLL : Box := (extendedBoxLLLL.bisect 1).1

private def extendedBoxLLLLR : Box := (extendedBoxLLLL.bisect 1).2

private def extendedBoxLLLLLL : Box := (extendedBoxLLLLL.bisect 2).1

private def extendedBoxLLLLLR : Box := (extendedBoxLLLLL.bisect 2).2

private def extendedBoxLLLLLLL : Box := (extendedBoxLLLLLL.bisect 0).1

private def extendedBoxLLLLLLR : Box := (extendedBoxLLLLLL.bisect 0).2

private def extendedBoxLLLLLLLL : Box := (extendedBoxLLLLLLL.bisect 1).1

private def extendedBoxLLLLLLLR : Box := (extendedBoxLLLLLLL.bisect 1).2

private def extendedTreeRootLLLLLLLL : Tree :=
  (.split 2
    .prune
    (.split 0
      (.split 1
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .leaf)
            (.split 1
              .leaf
              .leaf))
          (.split 0
            .leaf
            .leaf)))
      (.split 1
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .leaf)
            (.split 1
              .leaf
              .leaf))
          (.split 0
            .leaf
            .leaf))
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .leaf)
            (.split 1
              .leaf
              .leaf))
          (.split 0
            .leaf
            (.split 1
              .leaf
              .leaf))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLLL : Test extendedParameters extendedBoxLLLLLLLL :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLLL extendedBoxLLLLLLLL (by decide +kernel)

private def extendedBoxLLLLLLLRL : Box := (extendedBoxLLLLLLLR.bisect 2).1

private def extendedBoxLLLLLLLRR : Box := (extendedBoxLLLLLLLR.bisect 2).2

private def extendedTreeRootLLLLLLLRL : Tree :=
  (.split 0
    (.split 1
      (.split 2
        .prune
        (.split 0
          (.split 1
            .prune
            .leaf)
          .prune))
      (.split 2
        .prune
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))))
    (.split 1
      .prune
      (.split 2
        .prune
        (.split 0
          (.split 1
            .prune
            .leaf)
          .prune))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLLRL : Test extendedParameters extendedBoxLLLLLLLRL :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLLRL extendedBoxLLLLLLLRL (by decide +kernel)

private def extendedBoxLLLLLLLRRL : Box := (extendedBoxLLLLLLLRR.bisect 0).1

private def extendedBoxLLLLLLLRRR : Box := (extendedBoxLLLLLLLRR.bisect 0).2

private def extendedBoxLLLLLLLRRLL : Box := (extendedBoxLLLLLLLRRL.bisect 1).1

private def extendedBoxLLLLLLLRRLR : Box := (extendedBoxLLLLLLLRRL.bisect 1).2

private def extendedTreeRootLLLLLLLRRLL : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          .leaf
          .leaf)
        (.split 2
          .leaf
          .leaf))
      (.split 1
        (.split 2
          .leaf
          .leaf)
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)))
    (.split 0
      .leaf
      (.split 1
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLLRRLL : Test extendedParameters extendedBoxLLLLLLLRRLL :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLLRRLL extendedBoxLLLLLLLRRLL (by decide +kernel)

private def extendedTreeRootLLLLLLLRRLR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          .leaf
          .leaf)
        (.split 2
          .leaf
          .leaf))
      (.split 1
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)))
    (.split 0
      .leaf
      (.split 1
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLLRRLR : Test extendedParameters extendedBoxLLLLLLLRRLR :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLLRRLR extendedBoxLLLLLLLRRLR (by decide +kernel)

private theorem extendedTestRootLLLLLLLRRL : Test extendedParameters extendedBoxLLLLLLLRRL :=
  split_test (B := extendedBoxLLLLLLLRRL) 1 extendedTestRootLLLLLLLRRLL extendedTestRootLLLLLLLRRLR

private def extendedBoxLLLLLLLRRRL : Box := (extendedBoxLLLLLLLRRR.bisect 1).1

private def extendedBoxLLLLLLLRRRR : Box := (extendedBoxLLLLLLLRRR.bisect 1).2

private def extendedTreeRootLLLLLLLRRRL : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          .leaf
          .leaf)
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf))
      (.split 1
        (.split 2
          .leaf
          (.split 0
            .leaf
            .leaf))
        (.split 2
          (.split 0
            .leaf
            .leaf)
          (.split 0
            .leaf
            (.split 1
              .leaf
              .leaf)))))
    (.split 0
      (.split 1
        .leaf
        .leaf)
      (.split 1
        .leaf
        (.split 2
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLLRRRL : Test extendedParameters extendedBoxLLLLLLLRRRL :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLLRRRL extendedBoxLLLLLLLRRRL (by decide +kernel)

private def extendedBoxLLLLLLLRRRRL : Box := (extendedBoxLLLLLLLRRRR.bisect 2).1

private def extendedBoxLLLLLLLRRRRR : Box := (extendedBoxLLLLLLLRRRR.bisect 2).2

private def extendedTreeRootLLLLLLLRRRRL : Tree :=
  (.split 0
    (.split 1
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))
        .leaf)
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))
        .leaf))
    (.split 1
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))
        (.split 0
          .leaf
          (.split 1
            .leaf
            .leaf)))
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))
        (.split 0
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLLRRRRL : Test extendedParameters extendedBoxLLLLLLLRRRRL :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLLRRRRL extendedBoxLLLLLLLRRRRL (by decide +kernel)

private def extendedTreeRootLLLLLLLRRRRR : Tree :=
  (.split 0
    (.split 1
      .leaf
      .leaf)
    (.split 1
      (.split 2
        .leaf
        .leaf)
      .leaf))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLLRRRRR : Test extendedParameters extendedBoxLLLLLLLRRRRR :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLLRRRRR extendedBoxLLLLLLLRRRRR (by decide +kernel)

private theorem extendedTestRootLLLLLLLRRRR : Test extendedParameters extendedBoxLLLLLLLRRRR :=
  split_test (B := extendedBoxLLLLLLLRRRR) 2 extendedTestRootLLLLLLLRRRRL extendedTestRootLLLLLLLRRRRR

private theorem extendedTestRootLLLLLLLRRR : Test extendedParameters extendedBoxLLLLLLLRRR :=
  split_test (B := extendedBoxLLLLLLLRRR) 1 extendedTestRootLLLLLLLRRRL extendedTestRootLLLLLLLRRRR

private theorem extendedTestRootLLLLLLLRR : Test extendedParameters extendedBoxLLLLLLLRR :=
  split_test (B := extendedBoxLLLLLLLRR) 0 extendedTestRootLLLLLLLRRL extendedTestRootLLLLLLLRRR

private theorem extendedTestRootLLLLLLLR : Test extendedParameters extendedBoxLLLLLLLR :=
  split_test (B := extendedBoxLLLLLLLR) 2 extendedTestRootLLLLLLLRL extendedTestRootLLLLLLLRR

private theorem extendedTestRootLLLLLLL : Test extendedParameters extendedBoxLLLLLLL :=
  split_test (B := extendedBoxLLLLLLL) 1 extendedTestRootLLLLLLLL extendedTestRootLLLLLLLR

private def extendedBoxLLLLLLRL : Box := (extendedBoxLLLLLLR.bisect 1).1

private def extendedBoxLLLLLLRR : Box := (extendedBoxLLLLLLR.bisect 1).2

private def extendedBoxLLLLLLRLL : Box := (extendedBoxLLLLLLRL.bisect 2).1

private def extendedBoxLLLLLLRLR : Box := (extendedBoxLLLLLLRL.bisect 2).2

private def extendedTreeRootLLLLLLRLL : Tree :=
  .prune

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLRLL : Test extendedParameters extendedBoxLLLLLLRLL :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLRLL extendedBoxLLLLLLRLL (by decide +kernel)

private def extendedBoxLLLLLLRLRL : Box := (extendedBoxLLLLLLRLR.bisect 0).1

private def extendedBoxLLLLLLRLRR : Box := (extendedBoxLLLLLLRLR.bisect 0).2

private def extendedTreeRootLLLLLLRLRL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          (.split 2
            .prune
            (.split 0
              .leaf
              .leaf)))
        (.split 1
          .leaf
          (.split 2
            .leaf
            (.split 0
              .leaf
              .leaf))))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLRLRL : Test extendedParameters extendedBoxLLLLLLRLRL :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLRLRL extendedBoxLLLLLLRLRL (by decide +kernel)

private def extendedTreeRootLLLLLLRLRR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            .leaf
            (.split 0
              .leaf
              .leaf)))
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            .leaf
            .leaf)))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLRLRR : Test extendedParameters extendedBoxLLLLLLRLRR :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLRLRR extendedBoxLLLLLLRLRR (by decide +kernel)

private theorem extendedTestRootLLLLLLRLR : Test extendedParameters extendedBoxLLLLLLRLR :=
  split_test (B := extendedBoxLLLLLLRLR) 0 extendedTestRootLLLLLLRLRL extendedTestRootLLLLLLRLRR

private theorem extendedTestRootLLLLLLRL : Test extendedParameters extendedBoxLLLLLLRL :=
  split_test (B := extendedBoxLLLLLLRL) 2 extendedTestRootLLLLLLRLL extendedTestRootLLLLLLRLR

private def extendedBoxLLLLLLRRL : Box := (extendedBoxLLLLLLRR.bisect 2).1

private def extendedBoxLLLLLLRRR : Box := (extendedBoxLLLLLLRR.bisect 2).2

private def extendedTreeRootLLLLLLRRL : Tree :=
  .prune

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLRRL : Test extendedParameters extendedBoxLLLLLLRRL :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLRRL extendedBoxLLLLLLRRL (by decide +kernel)

private def extendedBoxLLLLLLRRRL : Box := (extendedBoxLLLLLLRRR.bisect 0).1

private def extendedBoxLLLLLLRRRR : Box := (extendedBoxLLLLLLRRR.bisect 0).2

private def extendedBoxLLLLLLRRRLL : Box := (extendedBoxLLLLLLRRRL.bisect 1).1

private def extendedBoxLLLLLLRRRLR : Box := (extendedBoxLLLLLLRRRL.bisect 1).2

private def extendedBoxLLLLLLRRRLLL : Box := (extendedBoxLLLLLLRRRLL.bisect 2).1

private def extendedBoxLLLLLLRRRLLR : Box := (extendedBoxLLLLLLRRRLL.bisect 2).2

private def extendedTreeRootLLLLLLRRRLLL : Tree :=
  (.split 0
    (.split 1
      (.split 2
        .prune
        (.split 0
          .leaf
          .leaf))
      (.split 2
        (.split 0
          .leaf
          .leaf)
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))))
    (.split 1
      (.split 2
        .prune
        (.split 0
          .leaf
          (.split 1
            .leaf
            .leaf)))
      (.split 2
        .prune
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf)))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLRRRLLL : Test extendedParameters extendedBoxLLLLLLRRRLLL :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLRRRLLL extendedBoxLLLLLLRRRLLL (by decide +kernel)

private def extendedTreeRootLLLLLLRRRLLR : Tree :=
  (.split 0
    (.split 1
      (.split 2
        .leaf
        .leaf)
      (.split 2
        .leaf
        .leaf))
    (.split 1
      (.split 2
        .leaf
        .leaf)
      (.split 2
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLRRRLLR : Test extendedParameters extendedBoxLLLLLLRRRLLR :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLRRRLLR extendedBoxLLLLLLRRRLLR (by decide +kernel)

private theorem extendedTestRootLLLLLLRRRLL : Test extendedParameters extendedBoxLLLLLLRRRLL :=
  split_test (B := extendedBoxLLLLLLRRRLL) 2 extendedTestRootLLLLLLRRRLLL extendedTestRootLLLLLLRRRLLR

private def extendedBoxLLLLLLRRRLRL : Box := (extendedBoxLLLLLLRRRLR.bisect 2).1

private def extendedBoxLLLLLLRRRLRR : Box := (extendedBoxLLLLLLRRRLR.bisect 2).2

private def extendedBoxLLLLLLRRRLRLL : Box := (extendedBoxLLLLLLRRRLRL.bisect 0).1

private def extendedBoxLLLLLLRRRLRLR : Box := (extendedBoxLLLLLLRRRLRL.bisect 0).2

private def extendedTreeRootLLLLLLRRRLRLL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        .leaf)
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLRRRLRLL : Test extendedParameters extendedBoxLLLLLLRRRLRLL :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLRRRLRLL extendedBoxLLLLLLRRRLRLL (by decide +kernel)

private def extendedTreeRootLLLLLLRRRLRLR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        .leaf
        .leaf)
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        .leaf
        .leaf)
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLRRRLRLR : Test extendedParameters extendedBoxLLLLLLRRRLRLR :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLRRRLRLR extendedBoxLLLLLLRRRLRLR (by decide +kernel)

private theorem extendedTestRootLLLLLLRRRLRL : Test extendedParameters extendedBoxLLLLLLRRRLRL :=
  split_test (B := extendedBoxLLLLLLRRRLRL) 0 extendedTestRootLLLLLLRRRLRLL extendedTestRootLLLLLLRRRLRLR

private def extendedTreeRootLLLLLLRRRLRR : Tree :=
  (.split 0
    (.split 1
      (.split 2
        .leaf
        .leaf)
      (.split 2
        .leaf
        .leaf))
    (.split 1
      (.split 2
        .leaf
        .leaf)
      (.split 2
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLRRRLRR : Test extendedParameters extendedBoxLLLLLLRRRLRR :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLRRRLRR extendedBoxLLLLLLRRRLRR (by decide +kernel)

private theorem extendedTestRootLLLLLLRRRLR : Test extendedParameters extendedBoxLLLLLLRRRLR :=
  split_test (B := extendedBoxLLLLLLRRRLR) 2 extendedTestRootLLLLLLRRRLRL extendedTestRootLLLLLLRRRLRR

private theorem extendedTestRootLLLLLLRRRL : Test extendedParameters extendedBoxLLLLLLRRRL :=
  split_test (B := extendedBoxLLLLLLRRRL) 1 extendedTestRootLLLLLLRRRLL extendedTestRootLLLLLLRRRLR

private def extendedBoxLLLLLLRRRRL : Box := (extendedBoxLLLLLLRRRR.bisect 1).1

private def extendedBoxLLLLLLRRRRR : Box := (extendedBoxLLLLLLRRRR.bisect 1).2

private def extendedBoxLLLLLLRRRRLL : Box := (extendedBoxLLLLLLRRRRL.bisect 2).1

private def extendedBoxLLLLLLRRRRLR : Box := (extendedBoxLLLLLLRRRRL.bisect 2).2

private def extendedTreeRootLLLLLLRRRRLL : Tree :=
  (.split 0
    (.split 1
      (.split 2
        .leaf
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf)))
      (.split 2
        .prune
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))))
    (.split 1
      (.split 2
        .leaf
        (.split 0
          .leaf
          .leaf))
      (.split 2
        .leaf
        (.split 0
          (.split 1
            .leaf
            .leaf)
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLRRRRLL : Test extendedParameters extendedBoxLLLLLLRRRRLL :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLRRRRLL extendedBoxLLLLLLRRRRLL (by decide +kernel)

private def extendedTreeRootLLLLLLRRRRLR : Tree :=
  (.split 0
    (.split 1
      (.split 2
        .leaf
        .leaf)
      (.split 2
        .leaf
        .leaf))
    (.split 1
      (.split 2
        .leaf
        .leaf)
      (.split 2
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLRRRRLR : Test extendedParameters extendedBoxLLLLLLRRRRLR :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLRRRRLR extendedBoxLLLLLLRRRRLR (by decide +kernel)

private theorem extendedTestRootLLLLLLRRRRL : Test extendedParameters extendedBoxLLLLLLRRRRL :=
  split_test (B := extendedBoxLLLLLLRRRRL) 2 extendedTestRootLLLLLLRRRRLL extendedTestRootLLLLLLRRRRLR

private def extendedTreeRootLLLLLLRRRRR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          .prune
          (.split 0
            (.split 1
              .leaf
              .leaf)
            .leaf))
        (.split 2
          (.split 0
            .leaf
            .leaf)
          (.split 0
            (.split 1
              .leaf
              .leaf)
            (.split 1
              .leaf
              .leaf))))
      (.split 1
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf))
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf))))
    (.split 0
      (.split 1
        (.split 2
          .leaf
          .leaf)
        (.split 2
          .leaf
          .leaf))
      (.split 1
        (.split 2
          .leaf
          .leaf)
        (.split 2
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLLRRRRR : Test extendedParameters extendedBoxLLLLLLRRRRR :=
  Tree.sound extendedParameters extendedTreeRootLLLLLLRRRRR extendedBoxLLLLLLRRRRR (by decide +kernel)

private theorem extendedTestRootLLLLLLRRRR : Test extendedParameters extendedBoxLLLLLLRRRR :=
  split_test (B := extendedBoxLLLLLLRRRR) 1 extendedTestRootLLLLLLRRRRL extendedTestRootLLLLLLRRRRR

private theorem extendedTestRootLLLLLLRRR : Test extendedParameters extendedBoxLLLLLLRRR :=
  split_test (B := extendedBoxLLLLLLRRR) 0 extendedTestRootLLLLLLRRRL extendedTestRootLLLLLLRRRR

private theorem extendedTestRootLLLLLLRR : Test extendedParameters extendedBoxLLLLLLRR :=
  split_test (B := extendedBoxLLLLLLRR) 2 extendedTestRootLLLLLLRRL extendedTestRootLLLLLLRRR

private theorem extendedTestRootLLLLLLR : Test extendedParameters extendedBoxLLLLLLR :=
  split_test (B := extendedBoxLLLLLLR) 1 extendedTestRootLLLLLLRL extendedTestRootLLLLLLRR

private theorem extendedTestRootLLLLLL : Test extendedParameters extendedBoxLLLLLL :=
  split_test (B := extendedBoxLLLLLL) 0 extendedTestRootLLLLLLL extendedTestRootLLLLLLR

private def extendedBoxLLLLLRL : Box := (extendedBoxLLLLLR.bisect 0).1

private def extendedBoxLLLLLRR : Box := (extendedBoxLLLLLR.bisect 0).2

private def extendedTreeRootLLLLLRL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        .leaf))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf)))
      (.split 0
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLRL : Test extendedParameters extendedBoxLLLLLRL :=
  Tree.sound extendedParameters extendedTreeRootLLLLLRL extendedBoxLLLLLRL (by decide +kernel)

private def extendedBoxLLLLLRRL : Box := (extendedBoxLLLLLRR.bisect 1).1

private def extendedBoxLLLLLRRR : Box := (extendedBoxLLLLLRR.bisect 1).2

private def extendedTreeRootLLLLLRRL : Tree :=
  (.split 2
    (.split 0
      (.split 1
        .leaf
        (.split 2
          .leaf
          .leaf))
      (.split 1
        (.split 2
          .leaf
          .leaf)
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)))
    (.split 0
      (.split 1
        .leaf
        .leaf)
      (.split 1
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLRRL : Test extendedParameters extendedBoxLLLLLRRL :=
  Tree.sound extendedParameters extendedTreeRootLLLLLRRL extendedBoxLLLLLRRL (by decide +kernel)

private def extendedTreeRootLLLLLRRR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          (.split 0
            .leaf
            (.split 1
              .leaf
              .leaf))
          .leaf)
        (.split 2
          (.split 0
            .leaf
            (.split 1
              .leaf
              .leaf))
          .leaf))
      (.split 1
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .leaf)
            .leaf)
          .leaf)
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .leaf)
            .leaf)
          .leaf)))
    (.split 0
      (.split 1
        .leaf
        .leaf)
      (.split 1
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLLRRR : Test extendedParameters extendedBoxLLLLLRRR :=
  Tree.sound extendedParameters extendedTreeRootLLLLLRRR extendedBoxLLLLLRRR (by decide +kernel)

private theorem extendedTestRootLLLLLRR : Test extendedParameters extendedBoxLLLLLRR :=
  split_test (B := extendedBoxLLLLLRR) 1 extendedTestRootLLLLLRRL extendedTestRootLLLLLRRR

private theorem extendedTestRootLLLLLR : Test extendedParameters extendedBoxLLLLLR :=
  split_test (B := extendedBoxLLLLLR) 0 extendedTestRootLLLLLRL extendedTestRootLLLLLRR

private theorem extendedTestRootLLLLL : Test extendedParameters extendedBoxLLLLL :=
  split_test (B := extendedBoxLLLLL) 2 extendedTestRootLLLLLL extendedTestRootLLLLLR

private def extendedBoxLLLLRL : Box := (extendedBoxLLLLR.bisect 2).1

private def extendedBoxLLLLRR : Box := (extendedBoxLLLLR.bisect 2).2

private def extendedBoxLLLLRLL : Box := (extendedBoxLLLLRL.bisect 0).1

private def extendedBoxLLLLRLR : Box := (extendedBoxLLLLRL.bisect 0).2

private def extendedBoxLLLLRLLL : Box := (extendedBoxLLLLRLL.bisect 1).1

private def extendedBoxLLLLRLLR : Box := (extendedBoxLLLLRLL.bisect 1).2

private def extendedBoxLLLLRLLLL : Box := (extendedBoxLLLLRLLL.bisect 2).1

private def extendedBoxLLLLRLLLR : Box := (extendedBoxLLLLRLLL.bisect 2).2

private def extendedTreeRootLLLLRLLLL : Tree :=
  (.split 0
    (.split 1
      (.split 2
        .prune
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf)))
      (.split 2
        .prune
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))))
    (.split 1
      (.split 2
        .prune
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf)))
      (.split 2
        .prune
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf)))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLRLLLL : Test extendedParameters extendedBoxLLLLRLLLL :=
  Tree.sound extendedParameters extendedTreeRootLLLLRLLLL extendedBoxLLLLRLLLL (by decide +kernel)

private def extendedBoxLLLLRLLLRL : Box := (extendedBoxLLLLRLLLR.bisect 0).1

private def extendedBoxLLLLRLLLRR : Box := (extendedBoxLLLLRLLLR.bisect 0).2

private def extendedTreeRootLLLLRLLLRL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          .leaf)
        (.split 1
          (.split 2
            .leaf
            .leaf)
          .leaf))
      (.split 0
        .leaf
        .leaf))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      .leaf))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLRLLLRL : Test extendedParameters extendedBoxLLLLRLLLRL :=
  Tree.sound extendedParameters extendedTreeRootLLLLRLLLRL extendedBoxLLLLRLLLRL (by decide +kernel)

private def extendedTreeRootLLLLRLLLRR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf)
          (.split 2
            .leaf
            .leaf))
        (.split 1
          (.split 2
            (.split 0
              (.split 1
                .leaf
                .leaf)
              (.split 1
                .leaf
                .leaf))
            .leaf)
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf)))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          (.split 2
            .leaf
            .leaf)
          .leaf))
      .leaf))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLRLLLRR : Test extendedParameters extendedBoxLLLLRLLLRR :=
  Tree.sound extendedParameters extendedTreeRootLLLLRLLLRR extendedBoxLLLLRLLLRR (by decide +kernel)

private theorem extendedTestRootLLLLRLLLR : Test extendedParameters extendedBoxLLLLRLLLR :=
  split_test (B := extendedBoxLLLLRLLLR) 0 extendedTestRootLLLLRLLLRL extendedTestRootLLLLRLLLRR

private theorem extendedTestRootLLLLRLLL : Test extendedParameters extendedBoxLLLLRLLL :=
  split_test (B := extendedBoxLLLLRLLL) 2 extendedTestRootLLLLRLLLL extendedTestRootLLLLRLLLR

private def extendedTreeRootLLLLRLLR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf))
        .leaf)
      (.split 1
        (.split 2
          .prune
          (.split 0
            .leaf
            (.split 1
              .leaf
              .leaf)))
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf))))
    (.split 0
      (.split 1
        (.split 2
          .leaf
          .leaf)
        .leaf)
      (.split 1
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLRLLR : Test extendedParameters extendedBoxLLLLRLLR :=
  Tree.sound extendedParameters extendedTreeRootLLLLRLLR extendedBoxLLLLRLLR (by decide +kernel)

private theorem extendedTestRootLLLLRLL : Test extendedParameters extendedBoxLLLLRLL :=
  split_test (B := extendedBoxLLLLRLL) 1 extendedTestRootLLLLRLLL extendedTestRootLLLLRLLR

private def extendedBoxLLLLRLRL : Box := (extendedBoxLLLLRLR.bisect 1).1

private def extendedBoxLLLLRLRR : Box := (extendedBoxLLLLRLR.bisect 1).2

private def extendedBoxLLLLRLRLL : Box := (extendedBoxLLLLRLRL.bisect 2).1

private def extendedBoxLLLLRLRLR : Box := (extendedBoxLLLLRLRL.bisect 2).2

private def extendedTreeRootLLLLRLRLL : Tree :=
  (.split 0
    (.split 1
      (.split 2
        .prune
        (.split 0
          (.split 1
            .prune
            .leaf)
          .prune))
      (.split 2
        .prune
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))))
    (.split 1
      .prune
      (.split 2
        .prune
        (.split 0
          (.split 1
            .prune
            .leaf)
          .prune))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLRLRLL : Test extendedParameters extendedBoxLLLLRLRLL :=
  Tree.sound extendedParameters extendedTreeRootLLLLRLRLL extendedBoxLLLLRLRLL (by decide +kernel)

private def extendedBoxLLLLRLRLRL : Box := (extendedBoxLLLLRLRLR.bisect 0).1

private def extendedBoxLLLLRLRLRR : Box := (extendedBoxLLLLRLRLR.bisect 0).2

private def extendedBoxLLLLRLRLRLL : Box := (extendedBoxLLLLRLRLRL.bisect 1).1

private def extendedBoxLLLLRLRLRLR : Box := (extendedBoxLLLLRLRLRL.bisect 1).2

private def extendedTreeRootLLLLRLRLRLL : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .leaf)
            (.split 1
              .leaf
              .leaf))
          (.split 0
            .leaf
            .leaf))
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf))
      (.split 1
        (.split 2
          (.split 0
            .leaf
            .leaf)
          (.split 0
            .leaf
            .leaf))
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)))
    (.split 0
      (.split 1
        .leaf
        .leaf)
      (.split 1
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLRLRLRLL : Test extendedParameters extendedBoxLLLLRLRLRLL :=
  Tree.sound extendedParameters extendedTreeRootLLLLRLRLRLL extendedBoxLLLLRLRLRLL (by decide +kernel)

private def extendedTreeRootLLLLRLRLRLR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          .leaf
          .leaf)
        .leaf)
      (.split 1
        (.split 2
          .leaf
          .leaf)
        .leaf))
    (.split 0
      .leaf
      .leaf))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLRLRLRLR : Test extendedParameters extendedBoxLLLLRLRLRLR :=
  Tree.sound extendedParameters extendedTreeRootLLLLRLRLRLR extendedBoxLLLLRLRLRLR (by decide +kernel)

private theorem extendedTestRootLLLLRLRLRL : Test extendedParameters extendedBoxLLLLRLRLRL :=
  split_test (B := extendedBoxLLLLRLRLRL) 1 extendedTestRootLLLLRLRLRLL extendedTestRootLLLLRLRLRLR

private def extendedTreeRootLLLLRLRLRR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            (.split 0
              .leaf
              .leaf)
            (.split 0
              .leaf
              .leaf))
          (.split 2
            .leaf
            .leaf))
        (.split 1
          (.split 2
            .leaf
            (.split 0
              .leaf
              .leaf))
          (.split 2
            .leaf
            .leaf)))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLRLRLRR : Test extendedParameters extendedBoxLLLLRLRLRR :=
  Tree.sound extendedParameters extendedTreeRootLLLLRLRLRR extendedBoxLLLLRLRLRR (by decide +kernel)

private theorem extendedTestRootLLLLRLRLR : Test extendedParameters extendedBoxLLLLRLRLR :=
  split_test (B := extendedBoxLLLLRLRLR) 0 extendedTestRootLLLLRLRLRL extendedTestRootLLLLRLRLRR

private theorem extendedTestRootLLLLRLRL : Test extendedParameters extendedBoxLLLLRLRL :=
  split_test (B := extendedBoxLLLLRLRL) 2 extendedTestRootLLLLRLRLL extendedTestRootLLLLRLRLR

private def extendedBoxLLLLRLRRL : Box := (extendedBoxLLLLRLRR.bisect 2).1

private def extendedBoxLLLLRLRRR : Box := (extendedBoxLLLLRLRR.bisect 2).2

private def extendedTreeRootLLLLRLRRL : Tree :=
  (.split 0
    (.split 1
      (.split 2
        .prune
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf)))
      (.split 2
        .prune
        (.split 0
          .leaf
          .leaf)))
    (.split 1
      (.split 2
        .prune
        (.split 0
          .leaf
          .leaf))
      (.split 2
        .prune
        (.split 0
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLRLRRL : Test extendedParameters extendedBoxLLLLRLRRL :=
  Tree.sound extendedParameters extendedTreeRootLLLLRLRRL extendedBoxLLLLRLRRL (by decide +kernel)

private def extendedTreeRootLLLLRLRRR : Tree :=
  (.split 0
    (.split 1
      (.split 2
        (.split 0
          .leaf
          (.split 1
            .leaf
            .leaf))
        .leaf)
      (.split 2
        .leaf
        .leaf))
    (.split 1
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))
        .leaf)
      (.split 2
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLRLRRR : Test extendedParameters extendedBoxLLLLRLRRR :=
  Tree.sound extendedParameters extendedTreeRootLLLLRLRRR extendedBoxLLLLRLRRR (by decide +kernel)

private theorem extendedTestRootLLLLRLRR : Test extendedParameters extendedBoxLLLLRLRR :=
  split_test (B := extendedBoxLLLLRLRR) 2 extendedTestRootLLLLRLRRL extendedTestRootLLLLRLRRR

private theorem extendedTestRootLLLLRLR : Test extendedParameters extendedBoxLLLLRLR :=
  split_test (B := extendedBoxLLLLRLR) 1 extendedTestRootLLLLRLRL extendedTestRootLLLLRLRR

private theorem extendedTestRootLLLLRL : Test extendedParameters extendedBoxLLLLRL :=
  split_test (B := extendedBoxLLLLRL) 0 extendedTestRootLLLLRLL extendedTestRootLLLLRLR

private def extendedTreeRootLLLLRR : Tree :=
  (.split 0
    (.split 1
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))
        .leaf)
      (.split 2
        (.split 0
          .leaf
          .leaf)
        .leaf))
    (.split 1
      (.split 2
        (.split 0
          (.split 1
            (.split 2
              (.split 0
                .leaf
                .leaf)
              .leaf)
            .leaf)
          (.split 1
            (.split 2
              (.split 0
                .leaf
                .leaf)
              .leaf)
            .leaf))
        (.split 0
          .leaf
          (.split 1
            .leaf
            .leaf)))
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLLRR : Test extendedParameters extendedBoxLLLLRR :=
  Tree.sound extendedParameters extendedTreeRootLLLLRR extendedBoxLLLLRR (by decide +kernel)

private theorem extendedTestRootLLLLR : Test extendedParameters extendedBoxLLLLR :=
  split_test (B := extendedBoxLLLLR) 2 extendedTestRootLLLLRL extendedTestRootLLLLRR

private theorem extendedTestRootLLLL : Test extendedParameters extendedBoxLLLL :=
  split_test (B := extendedBoxLLLL) 1 extendedTestRootLLLLL extendedTestRootLLLLR

private def extendedBoxLLLRL : Box := (extendedBoxLLLR.bisect 1).1

private def extendedBoxLLLRR : Box := (extendedBoxLLLR.bisect 1).2

private def extendedBoxLLLRLL : Box := (extendedBoxLLLRL.bisect 2).1

private def extendedBoxLLLRLR : Box := (extendedBoxLLLRL.bisect 2).2

private def extendedBoxLLLRLLL : Box := (extendedBoxLLLRLL.bisect 0).1

private def extendedBoxLLLRLLR : Box := (extendedBoxLLLRLL.bisect 0).2

private def extendedBoxLLLRLLLL : Box := (extendedBoxLLLRLLL.bisect 1).1

private def extendedBoxLLLRLLLR : Box := (extendedBoxLLLRLLL.bisect 1).2

private def extendedBoxLLLRLLLLL : Box := (extendedBoxLLLRLLLL.bisect 2).1

private def extendedBoxLLLRLLLLR : Box := (extendedBoxLLLRLLLL.bisect 2).2

private def extendedTreeRootLLLRLLLLL : Tree :=
  (.split 0
    (.split 1
      (.split 2
        .prune
        (.split 0
          .prune
          .leaf))
      .prune)
    (.split 1
      .leaf
      .leaf))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRLLLLL : Test extendedParameters extendedBoxLLLRLLLLL :=
  Tree.sound extendedParameters extendedTreeRootLLLRLLLLL extendedBoxLLLRLLLLL (by decide +kernel)

private def extendedBoxLLLRLLLLRL : Box := (extendedBoxLLLRLLLLR.bisect 0).1

private def extendedBoxLLLRLLLLRR : Box := (extendedBoxLLLRLLLLR.bisect 0).2

private def extendedTreeRootLLLRLLLLRL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        .leaf))
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            .leaf
            .leaf))
        (.split 1
          .leaf
          (.split 2
            .leaf
            .leaf)))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRLLLLRL : Test extendedParameters extendedBoxLLLRLLLLRL :=
  Tree.sound extendedParameters extendedTreeRootLLLRLLLLRL extendedBoxLLLRLLLLRL (by decide +kernel)

private def extendedTreeRootLLLRLLLLRR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        .leaf)
      .leaf)
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRLLLLRR : Test extendedParameters extendedBoxLLLRLLLLRR :=
  Tree.sound extendedParameters extendedTreeRootLLLRLLLLRR extendedBoxLLLRLLLLRR (by decide +kernel)

private theorem extendedTestRootLLLRLLLLR : Test extendedParameters extendedBoxLLLRLLLLR :=
  split_test (B := extendedBoxLLLRLLLLR) 0 extendedTestRootLLLRLLLLRL extendedTestRootLLLRLLLLRR

private theorem extendedTestRootLLLRLLLL : Test extendedParameters extendedBoxLLLRLLLL :=
  split_test (B := extendedBoxLLLRLLLL) 2 extendedTestRootLLLRLLLLL extendedTestRootLLLRLLLLR

private def extendedBoxLLLRLLLRL : Box := (extendedBoxLLLRLLLR.bisect 2).1

private def extendedBoxLLLRLLLRR : Box := (extendedBoxLLLRLLLR.bisect 2).2

private def extendedTreeRootLLLRLLLRL : Tree :=
  .prune

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRLLLRL : Test extendedParameters extendedBoxLLLRLLLRL :=
  Tree.sound extendedParameters extendedTreeRootLLLRLLLRL extendedBoxLLLRLLLRL (by decide +kernel)

private def extendedBoxLLLRLLLRRL : Box := (extendedBoxLLLRLLLRR.bisect 0).1

private def extendedBoxLLLRLLLRRR : Box := (extendedBoxLLLRLLLRR.bisect 0).2

private def extendedBoxLLLRLLLRRLL : Box := (extendedBoxLLLRLLLRRL.bisect 1).1

private def extendedBoxLLLRLLLRRLR : Box := (extendedBoxLLLRLLLRRL.bisect 1).2

private def extendedTreeRootLLLRLLLRRLL : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          .leaf
          .leaf)
        (.split 2
          .leaf
          (.split 0
            .leaf
            .leaf)))
      (.split 1
        (.split 2
          .leaf
          .leaf)
        (.split 2
          .leaf
          .leaf)))
    (.split 0
      (.split 1
        .leaf
        (.split 2
          .leaf
          .leaf))
      (.split 1
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRLLLRRLL : Test extendedParameters extendedBoxLLLRLLLRRLL :=
  Tree.sound extendedParameters extendedTreeRootLLLRLLLRRLL extendedBoxLLLRLLLRRLL (by decide +kernel)

private def extendedTreeRootLLLRLLLRRLR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          .leaf
          (.split 0
            .leaf
            .leaf))
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf)))
      (.split 1
        (.split 2
          .leaf
          .leaf)
        .leaf))
    (.split 0
      (.split 1
        (.split 2
          .leaf
          .leaf)
        .leaf)
      (.split 1
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRLLLRRLR : Test extendedParameters extendedBoxLLLRLLLRRLR :=
  Tree.sound extendedParameters extendedTreeRootLLLRLLLRRLR extendedBoxLLLRLLLRRLR (by decide +kernel)

private theorem extendedTestRootLLLRLLLRRL : Test extendedParameters extendedBoxLLLRLLLRRL :=
  split_test (B := extendedBoxLLLRLLLRRL) 1 extendedTestRootLLLRLLLRRLL extendedTestRootLLLRLLLRRLR

private def extendedTreeRootLLLRLLLRRR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            .leaf
            .leaf))
        (.split 1
          .leaf
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        .leaf))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRLLLRRR : Test extendedParameters extendedBoxLLLRLLLRRR :=
  Tree.sound extendedParameters extendedTreeRootLLLRLLLRRR extendedBoxLLLRLLLRRR (by decide +kernel)

private theorem extendedTestRootLLLRLLLRR : Test extendedParameters extendedBoxLLLRLLLRR :=
  split_test (B := extendedBoxLLLRLLLRR) 0 extendedTestRootLLLRLLLRRL extendedTestRootLLLRLLLRRR

private theorem extendedTestRootLLLRLLLR : Test extendedParameters extendedBoxLLLRLLLR :=
  split_test (B := extendedBoxLLLRLLLR) 2 extendedTestRootLLLRLLLRL extendedTestRootLLLRLLLRR

private theorem extendedTestRootLLLRLLL : Test extendedParameters extendedBoxLLLRLLL :=
  split_test (B := extendedBoxLLLRLLL) 1 extendedTestRootLLLRLLLL extendedTestRootLLLRLLLR

private def extendedBoxLLLRLLRL : Box := (extendedBoxLLLRLLR.bisect 1).1

private def extendedBoxLLLRLLRR : Box := (extendedBoxLLLRLLR.bisect 1).2

private def extendedTreeRootLLLRLLRL : Tree :=
  (.split 2
    (.split 0
      (.split 1
        .leaf
        .leaf)
      (.split 1
        .leaf
        .leaf))
    (.split 0
      (.split 1
        (.split 2
          .leaf
          .leaf)
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf))
      (.split 1
        .leaf
        (.split 2
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRLLRL : Test extendedParameters extendedBoxLLLRLLRL :=
  Tree.sound extendedParameters extendedTreeRootLLLRLLRL extendedBoxLLLRLLRL (by decide +kernel)

private def extendedTreeRootLLLRLLRR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        .leaf
        .prune)
      (.split 1
        .leaf
        .leaf))
    (.split 0
      (.split 1
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .leaf)
            .leaf)
          .leaf)
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .leaf)
            (.split 1
              .leaf
              .leaf))
          (.split 0
            .leaf
            .leaf)))
      (.split 1
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRLLRR : Test extendedParameters extendedBoxLLLRLLRR :=
  Tree.sound extendedParameters extendedTreeRootLLLRLLRR extendedBoxLLLRLLRR (by decide +kernel)

private theorem extendedTestRootLLLRLLR : Test extendedParameters extendedBoxLLLRLLR :=
  split_test (B := extendedBoxLLLRLLR) 1 extendedTestRootLLLRLLRL extendedTestRootLLLRLLRR

private theorem extendedTestRootLLLRLL : Test extendedParameters extendedBoxLLLRLL :=
  split_test (B := extendedBoxLLLRLL) 0 extendedTestRootLLLRLLL extendedTestRootLLLRLLR

private def extendedBoxLLLRLRL : Box := (extendedBoxLLLRLR.bisect 0).1

private def extendedBoxLLLRLRR : Box := (extendedBoxLLLRLR.bisect 0).2

private def extendedTreeRootLLLRLRL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          (.split 2
            .leaf
            .leaf))
        (.split 1
          .leaf
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf)
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf))
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            .leaf
            .leaf)))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRLRL : Test extendedParameters extendedBoxLLLRLRL :=
  Tree.sound extendedParameters extendedTreeRootLLLRLRL extendedBoxLLLRLRL (by decide +kernel)

private def extendedTreeRootLLLRLRR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        .leaf))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRLRR : Test extendedParameters extendedBoxLLLRLRR :=
  Tree.sound extendedParameters extendedTreeRootLLLRLRR extendedBoxLLLRLRR (by decide +kernel)

private theorem extendedTestRootLLLRLR : Test extendedParameters extendedBoxLLLRLR :=
  split_test (B := extendedBoxLLLRLR) 0 extendedTestRootLLLRLRL extendedTestRootLLLRLRR

private theorem extendedTestRootLLLRL : Test extendedParameters extendedBoxLLLRL :=
  split_test (B := extendedBoxLLLRL) 2 extendedTestRootLLLRLL extendedTestRootLLLRLR

private def extendedBoxLLLRRL : Box := (extendedBoxLLLRR.bisect 2).1

private def extendedBoxLLLRRR : Box := (extendedBoxLLLRR.bisect 2).2

private def extendedBoxLLLRRLL : Box := (extendedBoxLLLRRL.bisect 0).1

private def extendedBoxLLLRRLR : Box := (extendedBoxLLLRRL.bisect 0).2

private def extendedBoxLLLRRLLL : Box := (extendedBoxLLLRRLL.bisect 1).1

private def extendedBoxLLLRRLLR : Box := (extendedBoxLLLRRLL.bisect 1).2

private def extendedBoxLLLRRLLLL : Box := (extendedBoxLLLRRLLL.bisect 2).1

private def extendedBoxLLLRRLLLR : Box := (extendedBoxLLLRRLLL.bisect 2).2

private def extendedTreeRootLLLRRLLLL : Tree :=
  .prune

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRRLLLL : Test extendedParameters extendedBoxLLLRRLLLL :=
  Tree.sound extendedParameters extendedTreeRootLLLRRLLLL extendedBoxLLLRRLLLL (by decide +kernel)

private def extendedBoxLLLRRLLLRL : Box := (extendedBoxLLLRRLLLR.bisect 0).1

private def extendedBoxLLLRRLLLRR : Box := (extendedBoxLLLRRLLLR.bisect 0).2

private def extendedTreeRootLLLRRLLLRL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRRLLLRL : Test extendedParameters extendedBoxLLLRRLLLRL :=
  Tree.sound extendedParameters extendedTreeRootLLLRRLLLRL extendedBoxLLLRRLLLRL (by decide +kernel)

private def extendedTreeRootLLLRRLLLRR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        .leaf))
    (.split 2
      (.split 0
        .leaf
        .leaf)
      (.split 0
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRRLLLRR : Test extendedParameters extendedBoxLLLRRLLLRR :=
  Tree.sound extendedParameters extendedTreeRootLLLRRLLLRR extendedBoxLLLRRLLLRR (by decide +kernel)

private theorem extendedTestRootLLLRRLLLR : Test extendedParameters extendedBoxLLLRRLLLR :=
  split_test (B := extendedBoxLLLRRLLLR) 0 extendedTestRootLLLRRLLLRL extendedTestRootLLLRRLLLRR

private theorem extendedTestRootLLLRRLLL : Test extendedParameters extendedBoxLLLRRLLL :=
  split_test (B := extendedBoxLLLRRLLL) 2 extendedTestRootLLLRRLLLL extendedTestRootLLLRRLLLR

private def extendedTreeRootLLLRRLLR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          .prune
          (.split 0
            .leaf
            .prune))
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf)))
      (.split 1
        .prune
        .leaf))
    (.split 0
      (.split 1
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .leaf)
            .leaf)
          .leaf)
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf))
      (.split 1
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRRLLR : Test extendedParameters extendedBoxLLLRRLLR :=
  Tree.sound extendedParameters extendedTreeRootLLLRRLLR extendedBoxLLLRRLLR (by decide +kernel)

private theorem extendedTestRootLLLRRLL : Test extendedParameters extendedBoxLLLRRLL :=
  split_test (B := extendedBoxLLLRRLL) 1 extendedTestRootLLLRRLLL extendedTestRootLLLRRLLR

private def extendedTreeRootLLLRRLR : Tree :=
  (.split 1
    (.split 2
      .prune
      (.split 0
        (.split 1
          (.split 2
            (.split 0
              (.split 1
                .leaf
                .leaf)
              .leaf)
            (.split 0
              .leaf
              .leaf))
          (.split 2
            (.split 0
              .leaf
              .leaf)
            (.split 0
              .leaf
              .leaf)))
        (.split 1
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf)
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf))))
    (.split 2
      .prune
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          .leaf)
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRRLR : Test extendedParameters extendedBoxLLLRRLR :=
  Tree.sound extendedParameters extendedTreeRootLLLRRLR extendedBoxLLLRRLR (by decide +kernel)

private theorem extendedTestRootLLLRRL : Test extendedParameters extendedBoxLLLRRL :=
  split_test (B := extendedBoxLLLRRL) 0 extendedTestRootLLLRRLL extendedTestRootLLLRRLR

private def extendedBoxLLLRRRL : Box := (extendedBoxLLLRRR.bisect 0).1

private def extendedBoxLLLRRRR : Box := (extendedBoxLLLRRR.bisect 0).2

private def extendedTreeRootLLLRRRL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf)
          .leaf)
        (.split 1
          (.split 2
            .leaf
            .leaf)
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRRRL : Test extendedParameters extendedBoxLLLRRRL :=
  Tree.sound extendedParameters extendedTreeRootLLLRRRL extendedBoxLLLRRRL (by decide +kernel)

private def extendedTreeRootLLLRRRR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        .leaf))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        .leaf)
      .leaf))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLLRRRR : Test extendedParameters extendedBoxLLLRRRR :=
  Tree.sound extendedParameters extendedTreeRootLLLRRRR extendedBoxLLLRRRR (by decide +kernel)

private theorem extendedTestRootLLLRRR : Test extendedParameters extendedBoxLLLRRR :=
  split_test (B := extendedBoxLLLRRR) 0 extendedTestRootLLLRRRL extendedTestRootLLLRRRR

private theorem extendedTestRootLLLRR : Test extendedParameters extendedBoxLLLRR :=
  split_test (B := extendedBoxLLLRR) 2 extendedTestRootLLLRRL extendedTestRootLLLRRR

private theorem extendedTestRootLLLR : Test extendedParameters extendedBoxLLLR :=
  split_test (B := extendedBoxLLLR) 1 extendedTestRootLLLRL extendedTestRootLLLRR

private theorem extendedTestRootLLL : Test extendedParameters extendedBoxLLL :=
  split_test (B := extendedBoxLLL) 0 extendedTestRootLLLL extendedTestRootLLLR

private def extendedBoxLLRL : Box := (extendedBoxLLR.bisect 0).1

private def extendedBoxLLRR : Box := (extendedBoxLLR.bisect 0).2

private def extendedTreeRootLLRL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            .leaf
            .leaf)))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLRL : Test extendedParameters extendedBoxLLRL :=
  Tree.sound extendedParameters extendedTreeRootLLRL extendedBoxLLRL (by decide +kernel)

private def extendedTreeRootLLRR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf))
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            .leaf
            .leaf)))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          .leaf)
        (.split 1
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf)
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLLRR : Test extendedParameters extendedBoxLLRR :=
  Tree.sound extendedParameters extendedTreeRootLLRR extendedBoxLLRR (by decide +kernel)

private theorem extendedTestRootLLR : Test extendedParameters extendedBoxLLR :=
  split_test (B := extendedBoxLLR) 0 extendedTestRootLLRL extendedTestRootLLRR

private theorem extendedTestRootLL : Test extendedParameters extendedBoxLL :=
  split_test (B := extendedBoxLL) 2 extendedTestRootLLL extendedTestRootLLR

private def extendedBoxLRL : Box := (extendedBoxLR.bisect 2).1

private def extendedBoxLRR : Box := (extendedBoxLR.bisect 2).2

private def extendedBoxLRLL : Box := (extendedBoxLRL.bisect 0).1

private def extendedBoxLRLR : Box := (extendedBoxLRL.bisect 0).2

private def extendedBoxLRLLL : Box := (extendedBoxLRLL.bisect 1).1

private def extendedBoxLRLLR : Box := (extendedBoxLRLL.bisect 1).2

private def extendedBoxLRLLLL : Box := (extendedBoxLRLLL.bisect 2).1

private def extendedBoxLRLLLR : Box := (extendedBoxLRLLL.bisect 2).2

private def extendedTreeRootLRLLLL : Tree :=
  (.split 0
    (.split 1
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))
        (.split 0
          .leaf
          (.split 1
            .leaf
            .leaf)))
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))
        .leaf))
    (.split 1
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf)))
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          .leaf)
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLRLLLL : Test extendedParameters extendedBoxLRLLLL :=
  Tree.sound extendedParameters extendedTreeRootLRLLLL extendedBoxLRLLLL (by decide +kernel)

private def extendedTreeRootLRLLLR : Tree :=
  (.split 0
    (.split 1
      .leaf
      .leaf)
    (.split 1
      (.split 2
        .leaf
        .leaf)
      .leaf))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLRLLLR : Test extendedParameters extendedBoxLRLLLR :=
  Tree.sound extendedParameters extendedTreeRootLRLLLR extendedBoxLRLLLR (by decide +kernel)

private theorem extendedTestRootLRLLL : Test extendedParameters extendedBoxLRLLL :=
  split_test (B := extendedBoxLRLLL) 2 extendedTestRootLRLLLL extendedTestRootLRLLLR

private def extendedTreeRootLRLLR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          .leaf
          .leaf)
        .leaf)
      .leaf)
    .leaf)

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLRLLR : Test extendedParameters extendedBoxLRLLR :=
  Tree.sound extendedParameters extendedTreeRootLRLLR extendedBoxLRLLR (by decide +kernel)

private theorem extendedTestRootLRLL : Test extendedParameters extendedBoxLRLL :=
  split_test (B := extendedBoxLRLL) 1 extendedTestRootLRLLL extendedTestRootLRLLR

private def extendedTreeRootLRLR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            (.split 0
              (.split 1
                .leaf
                .leaf)
              (.split 1
                .leaf
                .leaf))
            (.split 0
              (.split 1
                .leaf
                .leaf)
              (.split 1
                .leaf
                .leaf)))
          (.split 2
            .leaf
            .leaf))
        (.split 1
          (.split 2
            .leaf
            (.split 0
              .leaf
              .leaf))
          .leaf))
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          .leaf)
        .leaf))
    .leaf)

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLRLR : Test extendedParameters extendedBoxLRLR :=
  Tree.sound extendedParameters extendedTreeRootLRLR extendedBoxLRLR (by decide +kernel)

private theorem extendedTestRootLRL : Test extendedParameters extendedBoxLRL :=
  split_test (B := extendedBoxLRL) 0 extendedTestRootLRLL extendedTestRootLRLR

private def extendedTreeRootLRR : Tree :=
  (.split 0
    (.split 1
      (.split 2
        .leaf
        .leaf)
      .leaf)
    (.split 1
      (.split 2
        .leaf
        .leaf)
      .leaf))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootLRR : Test extendedParameters extendedBoxLRR :=
  Tree.sound extendedParameters extendedTreeRootLRR extendedBoxLRR (by decide +kernel)

private theorem extendedTestRootLR : Test extendedParameters extendedBoxLR :=
  split_test (B := extendedBoxLR) 2 extendedTestRootLRL extendedTestRootLRR

private theorem extendedTestRootL : Test extendedParameters extendedBoxL :=
  split_test (B := extendedBoxL) 1 extendedTestRootLL extendedTestRootLR

private def extendedBoxRL : Box := (extendedBoxR.bisect 1).1

private def extendedBoxRR : Box := (extendedBoxR.bisect 1).2

private def extendedBoxRLL : Box := (extendedBoxRL.bisect 2).1

private def extendedBoxRLR : Box := (extendedBoxRL.bisect 2).2

private def extendedBoxRLLL : Box := (extendedBoxRLL.bisect 0).1

private def extendedBoxRLLR : Box := (extendedBoxRLL.bisect 0).2

private def extendedBoxRLLLL : Box := (extendedBoxRLLL.bisect 1).1

private def extendedBoxRLLLR : Box := (extendedBoxRLLL.bisect 1).2

private def extendedBoxRLLLLL : Box := (extendedBoxRLLLL.bisect 2).1

private def extendedBoxRLLLLR : Box := (extendedBoxRLLLL.bisect 2).2

private def extendedBoxRLLLLLL : Box := (extendedBoxRLLLLL.bisect 0).1

private def extendedBoxRLLLLLR : Box := (extendedBoxRLLLLL.bisect 0).2

private def extendedTreeRootRLLLLLL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        .leaf)
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf))
        (.split 1
          .leaf
          (.split 2
            .leaf
            .leaf)))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootRLLLLLL : Test extendedParameters extendedBoxRLLLLLL :=
  Tree.sound extendedParameters extendedTreeRootRLLLLLL extendedBoxRLLLLLL (by decide +kernel)

private def extendedTreeRootRLLLLLR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        .leaf
        .leaf)
      (.split 0
        .leaf
        .leaf))
    (.split 2
      (.split 0
        .leaf
        .leaf)
      (.split 0
        (.split 1
          .leaf
          .leaf)
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootRLLLLLR : Test extendedParameters extendedBoxRLLLLLR :=
  Tree.sound extendedParameters extendedTreeRootRLLLLLR extendedBoxRLLLLLR (by decide +kernel)

private theorem extendedTestRootRLLLLL : Test extendedParameters extendedBoxRLLLLL :=
  split_test (B := extendedBoxRLLLLL) 0 extendedTestRootRLLLLLL extendedTestRootRLLLLLR

private def extendedTreeRootRLLLLR : Tree :=
  (.split 0
    (.split 1
      (.split 2
        (.split 0
          .leaf
          .leaf)
        .leaf)
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          .leaf)
        (.split 0
          .leaf
          .leaf)))
    (.split 1
      (.split 2
        .leaf
        .leaf)
      (.split 2
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootRLLLLR : Test extendedParameters extendedBoxRLLLLR :=
  Tree.sound extendedParameters extendedTreeRootRLLLLR extendedBoxRLLLLR (by decide +kernel)

private theorem extendedTestRootRLLLL : Test extendedParameters extendedBoxRLLLL :=
  split_test (B := extendedBoxRLLLL) 2 extendedTestRootRLLLLL extendedTestRootRLLLLR

private def extendedTreeRootRLLLR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .prune)
            .leaf)
          (.split 0
            (.split 1
              (.split 2
                (.split 0
                  .leaf
                  .leaf)
                .leaf)
              (.split 2
                .leaf
                .leaf))
            (.split 1
              .leaf
              .leaf)))
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf)))
      (.split 1
        (.split 2
          .leaf
          .leaf)
        .leaf))
    (.split 0
      (.split 1
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .leaf)
            .leaf)
          .leaf)
        .leaf)
      .leaf))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootRLLLR : Test extendedParameters extendedBoxRLLLR :=
  Tree.sound extendedParameters extendedTreeRootRLLLR extendedBoxRLLLR (by decide +kernel)

private theorem extendedTestRootRLLL : Test extendedParameters extendedBoxRLLL :=
  split_test (B := extendedBoxRLLL) 1 extendedTestRootRLLLL extendedTestRootRLLLR

private def extendedTreeRootRLLR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          .leaf)
        .leaf)
      (.split 0
        .leaf
        .leaf))
    .leaf)

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootRLLR : Test extendedParameters extendedBoxRLLR :=
  Tree.sound extendedParameters extendedTreeRootRLLR extendedBoxRLLR (by decide +kernel)

private theorem extendedTestRootRLL : Test extendedParameters extendedBoxRLL :=
  split_test (B := extendedBoxRLL) 0 extendedTestRootRLLL extendedTestRootRLLR

private def extendedTreeRootRLR : Tree :=
  (.split 0
    (.split 1
      (.split 2
        (.split 0
          (.split 1
            .leaf
            (.split 2
              .leaf
              .leaf))
          (.split 1
            .leaf
            .leaf))
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf)))
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          .leaf)
        (.split 0
          (.split 1
            .leaf
            .leaf)
          .leaf)))
    (.split 1
      (.split 2
        .leaf
        .leaf)
      .leaf))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootRLR : Test extendedParameters extendedBoxRLR :=
  Tree.sound extendedParameters extendedTreeRootRLR extendedBoxRLR (by decide +kernel)

private theorem extendedTestRootRL : Test extendedParameters extendedBoxRL :=
  split_test (B := extendedBoxRL) 2 extendedTestRootRLL extendedTestRootRLR

private def extendedTreeRootRR : Tree :=
  .leaf

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem extendedTestRootRR : Test extendedParameters extendedBoxRR :=
  Tree.sound extendedParameters extendedTreeRootRR extendedBoxRR (by decide +kernel)

private theorem extendedTestRootR : Test extendedParameters extendedBoxR :=
  split_test (B := extendedBoxR) 1 extendedTestRootRL extendedTestRootRR

private theorem extendedTestRoot : Test extendedParameters extendedBox :=
  split_test (B := extendedBox) 0 extendedTestRootL extendedTestRootR

theorem extended_test : HotBoxTest (1/4000) extendedLimit extendedHeight (3/7)
    (ShapeBox.root extendedHeight) := by
  simpa only [extendedBox, Test, Box.root_cast, extendedParameters, extendedLimit, extendedHeight,
    Parameters.margin, Parameters.limit, Parameters.height, Parameters.loss,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using extendedTestRoot

/-- The outer spectral margin, with the finite cover discharged. -/
theorem extended_outer {r m n q : ℝ}
    (hr : 1 ≤ r) (hrT : r ≤ 1+extendedLimit)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq : q ≤ 1)
    (houter : InOuterRegion extendedHeight m n q) (U : unitary Mat) :
    (1-m)^2/4000 < normalizedDeficit r U m n q :=
  extended_outer_normalizedDeficit extended_test hr hrT hm hmn hnq hq houter U

private theorem extended_exp_upper : Real.exp (29/600 : ℝ) ≤ 1 + extendedLimit := by
  have h :=
    Real.exp_bound' (x := 29/600) (by norm_num) (by norm_num) (n := 4) (by decide)
  exact h.trans (by norm_num [Finset.sum_range_succ, Nat.factorial, extendedLimit])

/-- The outer spectral margin in the original inverse temperature. -/
theorem extended_outer_beta {β m n q : ℝ}
    (hβ : 0 ≤ β) (hβmax : β ≤ 29/200)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq : q ≤ 1)
    (houter : InOuterRegion extendedHeight m n q) (U : unitary Mat) :
    (1-m)^2/4000 < normalizedDeficit (Real.exp (β/3)) U m n q :=
  extended_outer (Real.one_le_exp (by positivity))
    ((Real.exp_le_exp_of_le (by linarith only [hβmax])).trans extended_exp_upper)
    hm hmn hnq hq houter U

#print axioms extended_outer_beta

private def firstParameters : Parameters := ⟨1/2000, 7/143, 7856887/32652860, 1/2⟩

private def firstBox : Box := Box.root firstParameters.height

private def firstBoxL : Box := (firstBox.bisect 0).1

private def firstBoxR : Box := (firstBox.bisect 0).2

private def firstBoxLL : Box := (firstBoxL.bisect 1).1

private def firstBoxLR : Box := (firstBoxL.bisect 1).2

private def firstBoxLLL : Box := (firstBoxLL.bisect 2).1

private def firstBoxLLR : Box := (firstBoxLL.bisect 2).2

private def firstBoxLLLL : Box := (firstBoxLLL.bisect 0).1

private def firstBoxLLLR : Box := (firstBoxLLL.bisect 0).2

private def firstBoxLLLLL : Box := (firstBoxLLLL.bisect 1).1

private def firstBoxLLLLR : Box := (firstBoxLLLL.bisect 1).2

private def firstBoxLLLLLL : Box := (firstBoxLLLLL.bisect 2).1

private def firstBoxLLLLLR : Box := (firstBoxLLLLL.bisect 2).2

private def firstBoxLLLLLLL : Box := (firstBoxLLLLLL.bisect 0).1

private def firstBoxLLLLLLR : Box := (firstBoxLLLLLL.bisect 0).2

private def firstBoxLLLLLLLL : Box := (firstBoxLLLLLLL.bisect 1).1

private def firstBoxLLLLLLLR : Box := (firstBoxLLLLLLL.bisect 1).2

private def firstTreeRootLLLLLLLL : Tree :=
  (.split 2
    .prune
    (.split 0
      (.split 1
        (.split 2
          .leaf
          .leaf)
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf))
      (.split 1
        (.split 2
          (.split 0
            .leaf
            (.split 1
              .leaf
              .leaf))
          (.split 0
            .leaf
            .leaf))
        (.split 2
          (.split 0
            .leaf
            (.split 1
              .leaf
              .leaf))
          (.split 0
            .leaf
            (.split 1
              .leaf
              .leaf))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLLLLL : Test firstParameters firstBoxLLLLLLLL :=
  Tree.sound firstParameters firstTreeRootLLLLLLLL firstBoxLLLLLLLL (by decide +kernel)

private def firstBoxLLLLLLLRL : Box := (firstBoxLLLLLLLR.bisect 2).1

private def firstBoxLLLLLLLRR : Box := (firstBoxLLLLLLLR.bisect 2).2

private def firstTreeRootLLLLLLLRL : Tree :=
  (.split 0
    (.split 1
      .prune
      (.split 2
        .prune
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .prune
            .leaf))))
    .prune)

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLLLLRL : Test firstParameters firstBoxLLLLLLLRL :=
  Tree.sound firstParameters firstTreeRootLLLLLLLRL firstBoxLLLLLLLRL (by decide +kernel)

private def firstBoxLLLLLLLRRL : Box := (firstBoxLLLLLLLRR.bisect 0).1

private def firstBoxLLLLLLLRRR : Box := (firstBoxLLLLLLLRR.bisect 0).2

private def firstTreeRootLLLLLLLRRL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          (.split 2
            .leaf
            .leaf)))
      (.split 0
        .leaf
        .leaf))
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          .leaf)
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            .leaf
            .leaf)))
      (.split 0
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLLLLRRL : Test firstParameters firstBoxLLLLLLLRRL :=
  Tree.sound firstParameters firstTreeRootLLLLLLLRRL firstBoxLLLLLLLRRL (by decide +kernel)

private def firstBoxLLLLLLLRRRL : Box := (firstBoxLLLLLLLRRR.bisect 1).1

private def firstBoxLLLLLLLRRRR : Box := (firstBoxLLLLLLLRRR.bisect 1).2

private def firstTreeRootLLLLLLLRRRL : Tree :=
  (.split 2
    (.split 0
      (.split 1
        .leaf
        (.split 2
          .leaf
          .leaf))
      (.split 1
        .leaf
        (.split 2
          .leaf
          (.split 0
            .leaf
            .leaf))))
    (.split 0
      (.split 1
        .leaf
        .leaf)
      (.split 1
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLLLLRRRL : Test firstParameters firstBoxLLLLLLLRRRL :=
  Tree.sound firstParameters firstTreeRootLLLLLLLRRRL firstBoxLLLLLLLRRRL (by decide +kernel)

private def firstTreeRootLLLLLLLRRRR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          .leaf
          .leaf)
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf))
      (.split 1
        (.split 2
          (.split 0
            .leaf
            .leaf)
          (.split 0
            .leaf
            .leaf))
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)))
    (.split 0
      (.split 1
        .leaf
        .leaf)
      (.split 1
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLLLLRRRR : Test firstParameters firstBoxLLLLLLLRRRR :=
  Tree.sound firstParameters firstTreeRootLLLLLLLRRRR firstBoxLLLLLLLRRRR (by decide +kernel)

private theorem firstTestRootLLLLLLLRRR : Test firstParameters firstBoxLLLLLLLRRR :=
  split_test (B := firstBoxLLLLLLLRRR) 1 firstTestRootLLLLLLLRRRL firstTestRootLLLLLLLRRRR

private theorem firstTestRootLLLLLLLRR : Test firstParameters firstBoxLLLLLLLRR :=
  split_test (B := firstBoxLLLLLLLRR) 0 firstTestRootLLLLLLLRRL firstTestRootLLLLLLLRRR

private theorem firstTestRootLLLLLLLR : Test firstParameters firstBoxLLLLLLLR :=
  split_test (B := firstBoxLLLLLLLR) 2 firstTestRootLLLLLLLRL firstTestRootLLLLLLLRR

private theorem firstTestRootLLLLLLL : Test firstParameters firstBoxLLLLLLL :=
  split_test (B := firstBoxLLLLLLL) 1 firstTestRootLLLLLLLL firstTestRootLLLLLLLR

private def firstBoxLLLLLLRL : Box := (firstBoxLLLLLLR.bisect 1).1

private def firstBoxLLLLLLRR : Box := (firstBoxLLLLLLR.bisect 1).2

private def firstBoxLLLLLLRLL : Box := (firstBoxLLLLLLRL.bisect 2).1

private def firstBoxLLLLLLRLR : Box := (firstBoxLLLLLLRL.bisect 2).2

private def firstTreeRootLLLLLLRLL : Tree :=
  .prune

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLLLRLL : Test firstParameters firstBoxLLLLLLRLL :=
  Tree.sound firstParameters firstTreeRootLLLLLLRLL firstBoxLLLLLLRLL (by decide +kernel)

private def firstBoxLLLLLLRLRL : Box := (firstBoxLLLLLLRLR.bisect 0).1

private def firstBoxLLLLLLRLRR : Box := (firstBoxLLLLLLRLR.bisect 0).2

private def firstTreeRootLLLLLLRLRL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLLLRLRL : Test firstParameters firstBoxLLLLLLRLRL :=
  Tree.sound firstParameters firstTreeRootLLLLLLRLRL firstBoxLLLLLLRLRL (by decide +kernel)

private def firstTreeRootLLLLLLRLRR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        .leaf))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLLLRLRR : Test firstParameters firstBoxLLLLLLRLRR :=
  Tree.sound firstParameters firstTreeRootLLLLLLRLRR firstBoxLLLLLLRLRR (by decide +kernel)

private theorem firstTestRootLLLLLLRLR : Test firstParameters firstBoxLLLLLLRLR :=
  split_test (B := firstBoxLLLLLLRLR) 0 firstTestRootLLLLLLRLRL firstTestRootLLLLLLRLRR

private theorem firstTestRootLLLLLLRL : Test firstParameters firstBoxLLLLLLRL :=
  split_test (B := firstBoxLLLLLLRL) 2 firstTestRootLLLLLLRLL firstTestRootLLLLLLRLR

private def firstBoxLLLLLLRRL : Box := (firstBoxLLLLLLRR.bisect 2).1

private def firstBoxLLLLLLRRR : Box := (firstBoxLLLLLLRR.bisect 2).2

private def firstTreeRootLLLLLLRRL : Tree :=
  .prune

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLLLRRL : Test firstParameters firstBoxLLLLLLRRL :=
  Tree.sound firstParameters firstTreeRootLLLLLLRRL firstBoxLLLLLLRRL (by decide +kernel)

private def firstBoxLLLLLLRRRL : Box := (firstBoxLLLLLLRRR.bisect 0).1

private def firstBoxLLLLLLRRRR : Box := (firstBoxLLLLLLRRR.bisect 0).2

private def firstBoxLLLLLLRRRLL : Box := (firstBoxLLLLLLRRRL.bisect 1).1

private def firstBoxLLLLLLRRRLR : Box := (firstBoxLLLLLLRRRL.bisect 1).2

private def firstTreeRootLLLLLLRRRLL : Tree :=
  (.split 2
    (.split 0
      (.split 1
        .leaf
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf)))
      (.split 1
        .leaf
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf))))
    (.split 0
      (.split 1
        .leaf
        .leaf)
      (.split 1
        .leaf
        (.split 2
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLLLRRRLL : Test firstParameters firstBoxLLLLLLRRRLL :=
  Tree.sound firstParameters firstTreeRootLLLLLLRRRLL firstBoxLLLLLLRRRLL (by decide +kernel)

private def firstTreeRootLLLLLLRRRLR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          .leaf
          (.split 0
            .leaf
            .leaf))
        (.split 2
          (.split 0
            .leaf
            .leaf)
          (.split 0
            .leaf
            .leaf)))
      (.split 1
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf))
        (.split 2
          .leaf
          (.split 0
            .leaf
            .leaf))))
    (.split 0
      (.split 1
        .leaf
        .leaf)
      (.split 1
        (.split 2
          .leaf
          .leaf)
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLLLRRRLR : Test firstParameters firstBoxLLLLLLRRRLR :=
  Tree.sound firstParameters firstTreeRootLLLLLLRRRLR firstBoxLLLLLLRRRLR (by decide +kernel)

private theorem firstTestRootLLLLLLRRRL : Test firstParameters firstBoxLLLLLLRRRL :=
  split_test (B := firstBoxLLLLLLRRRL) 1 firstTestRootLLLLLLRRRLL firstTestRootLLLLLLRRRLR

private def firstBoxLLLLLLRRRRL : Box := (firstBoxLLLLLLRRRR.bisect 1).1

private def firstBoxLLLLLLRRRRR : Box := (firstBoxLLLLLLRRRR.bisect 1).2

private def firstTreeRootLLLLLLRRRRL : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf))
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf)))
      (.split 1
        (.split 2
          .leaf
          (.split 0
            .leaf
            .leaf))
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf))))
    (.split 0
      (.split 1
        .leaf
        (.split 2
          .leaf
          .leaf))
      (.split 1
        .leaf
        (.split 2
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLLLRRRRL : Test firstParameters firstBoxLLLLLLRRRRL :=
  Tree.sound firstParameters firstTreeRootLLLLLLRRRRL firstBoxLLLLLLRRRRL (by decide +kernel)

private def firstTreeRootLLLLLLRRRRR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        .leaf
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf)))
      (.split 1
        .leaf
        .leaf))
    (.split 0
      (.split 1
        (.split 2
          .leaf
          .leaf)
        .leaf)
      (.split 1
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLLLRRRRR : Test firstParameters firstBoxLLLLLLRRRRR :=
  Tree.sound firstParameters firstTreeRootLLLLLLRRRRR firstBoxLLLLLLRRRRR (by decide +kernel)

private theorem firstTestRootLLLLLLRRRR : Test firstParameters firstBoxLLLLLLRRRR :=
  split_test (B := firstBoxLLLLLLRRRR) 1 firstTestRootLLLLLLRRRRL firstTestRootLLLLLLRRRRR

private theorem firstTestRootLLLLLLRRR : Test firstParameters firstBoxLLLLLLRRR :=
  split_test (B := firstBoxLLLLLLRRR) 0 firstTestRootLLLLLLRRRL firstTestRootLLLLLLRRRR

private theorem firstTestRootLLLLLLRR : Test firstParameters firstBoxLLLLLLRR :=
  split_test (B := firstBoxLLLLLLRR) 2 firstTestRootLLLLLLRRL firstTestRootLLLLLLRRR

private theorem firstTestRootLLLLLLR : Test firstParameters firstBoxLLLLLLR :=
  split_test (B := firstBoxLLLLLLR) 1 firstTestRootLLLLLLRL firstTestRootLLLLLLRR

private theorem firstTestRootLLLLLL : Test firstParameters firstBoxLLLLLL :=
  split_test (B := firstBoxLLLLLL) 0 firstTestRootLLLLLLL firstTestRootLLLLLLR

private def firstBoxLLLLLRL : Box := (firstBoxLLLLLR.bisect 0).1

private def firstBoxLLLLLRR : Box := (firstBoxLLLLLR.bisect 0).2

private def firstTreeRootLLLLLRL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        .leaf))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            .leaf
            .leaf)))
      (.split 0
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLLRL : Test firstParameters firstBoxLLLLLRL :=
  Tree.sound firstParameters firstTreeRootLLLLLRL firstBoxLLLLLRL (by decide +kernel)

private def firstBoxLLLLLRRL : Box := (firstBoxLLLLLRR.bisect 1).1

private def firstBoxLLLLLRRR : Box := (firstBoxLLLLLRR.bisect 1).2

private def firstTreeRootLLLLLRRL : Tree :=
  (.split 2
    (.split 0
      (.split 1
        .leaf
        (.split 2
          .leaf
          .leaf))
      (.split 1
        .leaf
        (.split 2
          .leaf
          .leaf)))
    (.split 0
      (.split 1
        .leaf
        .leaf)
      (.split 1
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLLRRL : Test firstParameters firstBoxLLLLLRRL :=
  Tree.sound firstParameters firstTreeRootLLLLLRRL firstBoxLLLLLRRL (by decide +kernel)

private def firstTreeRootLLLLLRRR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf))
      (.split 1
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)))
    (.split 0
      (.split 1
        .leaf
        .leaf)
      (.split 1
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLLRRR : Test firstParameters firstBoxLLLLLRRR :=
  Tree.sound firstParameters firstTreeRootLLLLLRRR firstBoxLLLLLRRR (by decide +kernel)

private theorem firstTestRootLLLLLRR : Test firstParameters firstBoxLLLLLRR :=
  split_test (B := firstBoxLLLLLRR) 1 firstTestRootLLLLLRRL firstTestRootLLLLLRRR

private theorem firstTestRootLLLLLR : Test firstParameters firstBoxLLLLLR :=
  split_test (B := firstBoxLLLLLR) 0 firstTestRootLLLLLRL firstTestRootLLLLLRR

private theorem firstTestRootLLLLL : Test firstParameters firstBoxLLLLL :=
  split_test (B := firstBoxLLLLL) 2 firstTestRootLLLLLL firstTestRootLLLLLR

private def firstBoxLLLLRL : Box := (firstBoxLLLLR.bisect 2).1

private def firstBoxLLLLRR : Box := (firstBoxLLLLR.bisect 2).2

private def firstBoxLLLLRLL : Box := (firstBoxLLLLRL.bisect 0).1

private def firstBoxLLLLRLR : Box := (firstBoxLLLLRL.bisect 0).2

private def firstBoxLLLLRLLL : Box := (firstBoxLLLLRLL.bisect 1).1

private def firstBoxLLLLRLLR : Box := (firstBoxLLLLRLL.bisect 1).2

private def firstBoxLLLLRLLLL : Box := (firstBoxLLLLRLLL.bisect 2).1

private def firstBoxLLLLRLLLR : Box := (firstBoxLLLLRLLL.bisect 2).2

private def firstTreeRootLLLLRLLLL : Tree :=
  (.split 0
    (.split 1
      (.split 2
        .prune
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf)))
      (.split 2
        .prune
        (.split 0
          .leaf
          .leaf)))
    (.split 1
      (.split 2
        .prune
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .prune
            .leaf)))
      (.split 2
        .prune
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf)))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLRLLLL : Test firstParameters firstBoxLLLLRLLLL :=
  Tree.sound firstParameters firstTreeRootLLLLRLLLL firstBoxLLLLRLLLL (by decide +kernel)

private def firstBoxLLLLRLLLRL : Box := (firstBoxLLLLRLLLR.bisect 0).1

private def firstBoxLLLLRLLLRR : Box := (firstBoxLLLLRLLLR.bisect 0).2

private def firstTreeRootLLLLRLLLRL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        .leaf))
    (.split 2
      (.split 0
        .leaf
        .leaf)
      .leaf))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLRLLLRL : Test firstParameters firstBoxLLLLRLLLRL :=
  Tree.sound firstParameters firstTreeRootLLLLRLLLRL firstBoxLLLLRLLLRL (by decide +kernel)

private def firstTreeRootLLLLRLLLRR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          .leaf)
        (.split 1
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf)
          (.split 2
            .leaf
            .leaf)))
      (.split 0
        .leaf
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      .leaf))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLRLLLRR : Test firstParameters firstBoxLLLLRLLLRR :=
  Tree.sound firstParameters firstTreeRootLLLLRLLLRR firstBoxLLLLRLLLRR (by decide +kernel)

private theorem firstTestRootLLLLRLLLR : Test firstParameters firstBoxLLLLRLLLR :=
  split_test (B := firstBoxLLLLRLLLR) 0 firstTestRootLLLLRLLLRL firstTestRootLLLLRLLLRR

private theorem firstTestRootLLLLRLLL : Test firstParameters firstBoxLLLLRLLL :=
  split_test (B := firstBoxLLLLRLLL) 2 firstTestRootLLLLRLLLL firstTestRootLLLLRLLLR

private def firstTreeRootLLLLRLLR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf))
        .leaf)
      (.split 1
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf))
        .leaf))
    (.split 0
      (.split 1
        (.split 2
          .leaf
          .leaf)
        .leaf)
      (.split 1
        (.split 2
          .leaf
          .leaf)
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLRLLR : Test firstParameters firstBoxLLLLRLLR :=
  Tree.sound firstParameters firstTreeRootLLLLRLLR firstBoxLLLLRLLR (by decide +kernel)

private theorem firstTestRootLLLLRLL : Test firstParameters firstBoxLLLLRLL :=
  split_test (B := firstBoxLLLLRLL) 1 firstTestRootLLLLRLLL firstTestRootLLLLRLLR

private def firstBoxLLLLRLRL : Box := (firstBoxLLLLRLR.bisect 1).1

private def firstBoxLLLLRLRR : Box := (firstBoxLLLLRLR.bisect 1).2

private def firstBoxLLLLRLRLL : Box := (firstBoxLLLLRLRL.bisect 2).1

private def firstBoxLLLLRLRLR : Box := (firstBoxLLLLRLRL.bisect 2).2

private def firstTreeRootLLLLRLRLL : Tree :=
  (.split 0
    (.split 1
      .prune
      (.split 2
        .prune
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .prune
            .leaf))))
    .prune)

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLRLRLL : Test firstParameters firstBoxLLLLRLRLL :=
  Tree.sound firstParameters firstTreeRootLLLLRLRLL firstBoxLLLLRLRLL (by decide +kernel)

private def firstBoxLLLLRLRLRL : Box := (firstBoxLLLLRLRLR.bisect 0).1

private def firstBoxLLLLRLRLRR : Box := (firstBoxLLLLRLRLR.bisect 0).2

private def firstTreeRootLLLLRLRLRL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf)
          (.split 2
            .leaf
            .leaf))
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            .leaf
            .leaf)))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLRLRLRL : Test firstParameters firstBoxLLLLRLRLRL :=
  Tree.sound firstParameters firstTreeRootLLLLRLRLRL firstBoxLLLLRLRLRL (by decide +kernel)

private def firstTreeRootLLLLRLRLRR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLRLRLRR : Test firstParameters firstBoxLLLLRLRLRR :=
  Tree.sound firstParameters firstTreeRootLLLLRLRLRR firstBoxLLLLRLRLRR (by decide +kernel)

private theorem firstTestRootLLLLRLRLR : Test firstParameters firstBoxLLLLRLRLR :=
  split_test (B := firstBoxLLLLRLRLR) 0 firstTestRootLLLLRLRLRL firstTestRootLLLLRLRLRR

private theorem firstTestRootLLLLRLRL : Test firstParameters firstBoxLLLLRLRL :=
  split_test (B := firstBoxLLLLRLRL) 2 firstTestRootLLLLRLRLL firstTestRootLLLLRLRLR

private def firstTreeRootLLLLRLRR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf))
        .leaf)
      (.split 1
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf))
        .leaf))
    (.split 0
      (.split 1
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)
        .leaf)
      (.split 1
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)
        (.split 2
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLRLRR : Test firstParameters firstBoxLLLLRLRR :=
  Tree.sound firstParameters firstTreeRootLLLLRLRR firstBoxLLLLRLRR (by decide +kernel)

private theorem firstTestRootLLLLRLR : Test firstParameters firstBoxLLLLRLR :=
  split_test (B := firstBoxLLLLRLR) 1 firstTestRootLLLLRLRL firstTestRootLLLLRLRR

private theorem firstTestRootLLLLRL : Test firstParameters firstBoxLLLLRL :=
  split_test (B := firstBoxLLLLRL) 0 firstTestRootLLLLRLL firstTestRootLLLLRLR

private def firstTreeRootLLLLRR : Tree :=
  (.split 0
    (.split 1
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))
        .leaf)
      (.split 2
        (.split 0
          .leaf
          .leaf)
        .leaf))
    (.split 1
      (.split 2
        (.split 0
          (.split 1
            (.split 2
              .leaf
              .leaf)
            .leaf)
          (.split 1
            (.split 2
              .leaf
              .leaf)
            .leaf))
        (.split 0
          .leaf
          .leaf))
      (.split 2
        (.split 0
          .leaf
          (.split 1
            .leaf
            .leaf))
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLLRR : Test firstParameters firstBoxLLLLRR :=
  Tree.sound firstParameters firstTreeRootLLLLRR firstBoxLLLLRR (by decide +kernel)

private theorem firstTestRootLLLLR : Test firstParameters firstBoxLLLLR :=
  split_test (B := firstBoxLLLLR) 2 firstTestRootLLLLRL firstTestRootLLLLRR

private theorem firstTestRootLLLL : Test firstParameters firstBoxLLLL :=
  split_test (B := firstBoxLLLL) 1 firstTestRootLLLLL firstTestRootLLLLR

private def firstBoxLLLRL : Box := (firstBoxLLLR.bisect 1).1

private def firstBoxLLLRR : Box := (firstBoxLLLR.bisect 1).2

private def firstBoxLLLRLL : Box := (firstBoxLLLRL.bisect 2).1

private def firstBoxLLLRLR : Box := (firstBoxLLLRL.bisect 2).2

private def firstBoxLLLRLLL : Box := (firstBoxLLLRLL.bisect 0).1

private def firstBoxLLLRLLR : Box := (firstBoxLLLRLL.bisect 0).2

private def firstBoxLLLRLLLL : Box := (firstBoxLLLRLLL.bisect 1).1

private def firstBoxLLLRLLLR : Box := (firstBoxLLLRLLL.bisect 1).2

private def firstTreeRootLLLRLLLL : Tree :=
  (.split 2
    (.split 0
      .prune
      (.split 1
        .leaf
        .prune))
    (.split 0
      (.split 1
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .leaf)
            (.split 1
              .leaf
              .leaf))
          (.split 0
            .leaf
            .leaf))
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .leaf)
            (.split 1
              .leaf
              .leaf))
          (.split 0
            (.split 1
              .leaf
              .leaf)
            .leaf)))
      (.split 1
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .leaf)
            .leaf)
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLRLLLL : Test firstParameters firstBoxLLLRLLLL :=
  Tree.sound firstParameters firstTreeRootLLLRLLLL firstBoxLLLRLLLL (by decide +kernel)

private def firstBoxLLLRLLLRL : Box := (firstBoxLLLRLLLR.bisect 2).1

private def firstBoxLLLRLLLRR : Box := (firstBoxLLLRLLLR.bisect 2).2

private def firstTreeRootLLLRLLLRL : Tree :=
  .prune

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLRLLLRL : Test firstParameters firstBoxLLLRLLLRL :=
  Tree.sound firstParameters firstTreeRootLLLRLLLRL firstBoxLLLRLLLRL (by decide +kernel)

private def firstBoxLLLRLLLRRL : Box := (firstBoxLLLRLLLRR.bisect 0).1

private def firstBoxLLLRLLLRRR : Box := (firstBoxLLLRLLLRR.bisect 0).2

private def firstTreeRootLLLRLLLRRL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLRLLLRRL : Test firstParameters firstBoxLLLRLLLRRL :=
  Tree.sound firstParameters firstTreeRootLLLRLLLRRL firstBoxLLLRLLLRRL (by decide +kernel)

private def firstTreeRootLLLRLLLRRR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        .leaf))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLRLLLRRR : Test firstParameters firstBoxLLLRLLLRRR :=
  Tree.sound firstParameters firstTreeRootLLLRLLLRRR firstBoxLLLRLLLRRR (by decide +kernel)

private theorem firstTestRootLLLRLLLRR : Test firstParameters firstBoxLLLRLLLRR :=
  split_test (B := firstBoxLLLRLLLRR) 0 firstTestRootLLLRLLLRRL firstTestRootLLLRLLLRRR

private theorem firstTestRootLLLRLLLR : Test firstParameters firstBoxLLLRLLLR :=
  split_test (B := firstBoxLLLRLLLR) 2 firstTestRootLLLRLLLRL firstTestRootLLLRLLLRR

private theorem firstTestRootLLLRLLL : Test firstParameters firstBoxLLLRLLL :=
  split_test (B := firstBoxLLLRLLL) 1 firstTestRootLLLRLLLL firstTestRootLLLRLLLR

private def firstBoxLLLRLLRL : Box := (firstBoxLLLRLLR.bisect 1).1

private def firstBoxLLLRLLRR : Box := (firstBoxLLLRLLR.bisect 1).2

private def firstTreeRootLLLRLLRL : Tree :=
  (.split 2
    (.split 0
      (.split 1
        .leaf
        .leaf)
      (.split 1
        .leaf
        .leaf))
    (.split 0
      (.split 1
        (.split 2
          .leaf
          .leaf)
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf))
      (.split 1
        .leaf
        (.split 2
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLRLLRL : Test firstParameters firstBoxLLLRLLRL :=
  Tree.sound firstParameters firstTreeRootLLLRLLRL firstBoxLLLRLLRL (by decide +kernel)

private def firstTreeRootLLLRLLRR : Tree :=
  (.split 2
    (.split 0
      .prune
      (.split 1
        .leaf
        .prune))
    (.split 0
      (.split 1
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)
        (.split 2
          (.split 0
            .leaf
            .leaf)
          (.split 0
            .leaf
            .leaf)))
      (.split 1
        (.split 2
          .leaf
          .leaf)
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLRLLRR : Test firstParameters firstBoxLLLRLLRR :=
  Tree.sound firstParameters firstTreeRootLLLRLLRR firstBoxLLLRLLRR (by decide +kernel)

private theorem firstTestRootLLLRLLR : Test firstParameters firstBoxLLLRLLR :=
  split_test (B := firstBoxLLLRLLR) 1 firstTestRootLLLRLLRL firstTestRootLLLRLLRR

private theorem firstTestRootLLLRLL : Test firstParameters firstBoxLLLRLL :=
  split_test (B := firstBoxLLLRLL) 0 firstTestRootLLLRLLL firstTestRootLLLRLLR

private def firstBoxLLLRLRL : Box := (firstBoxLLLRLR.bisect 0).1

private def firstBoxLLLRLRR : Box := (firstBoxLLLRLR.bisect 0).2

private def firstTreeRootLLLRLRL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          (.split 2
            .leaf
            .leaf))
        (.split 1
          .leaf
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        .leaf))
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf)
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf))
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            .leaf
            .leaf)))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLRLRL : Test firstParameters firstBoxLLLRLRL :=
  Tree.sound firstParameters firstTreeRootLLLRLRL firstBoxLLLRLRL (by decide +kernel)

private def firstTreeRootLLLRLRR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        .leaf)
      (.split 0
        .leaf
        .leaf))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLRLRR : Test firstParameters firstBoxLLLRLRR :=
  Tree.sound firstParameters firstTreeRootLLLRLRR firstBoxLLLRLRR (by decide +kernel)

private theorem firstTestRootLLLRLR : Test firstParameters firstBoxLLLRLR :=
  split_test (B := firstBoxLLLRLR) 0 firstTestRootLLLRLRL firstTestRootLLLRLRR

private theorem firstTestRootLLLRL : Test firstParameters firstBoxLLLRL :=
  split_test (B := firstBoxLLLRL) 2 firstTestRootLLLRLL firstTestRootLLLRLR

private def firstBoxLLLRRL : Box := (firstBoxLLLRR.bisect 2).1

private def firstBoxLLLRRR : Box := (firstBoxLLLRR.bisect 2).2

private def firstBoxLLLRRLL : Box := (firstBoxLLLRRL.bisect 0).1

private def firstBoxLLLRRLR : Box := (firstBoxLLLRRL.bisect 0).2

private def firstBoxLLLRRLLL : Box := (firstBoxLLLRRLL.bisect 1).1

private def firstBoxLLLRRLLR : Box := (firstBoxLLLRRLL.bisect 1).2

private def firstTreeRootLLLRRLLL : Tree :=
  (.split 2
    .prune
    (.split 0
      (.split 1
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .leaf)
            (.split 1
              .leaf
              .leaf))
          (.split 0
            (.split 1
              .leaf
              .leaf)
            (.split 1
              .leaf
              .leaf)))
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .leaf)
            .leaf)
          (.split 0
            .leaf
            .leaf)))
      (.split 1
        (.split 2
          (.split 0
            .leaf
            .leaf)
          (.split 0
            .leaf
            .leaf))
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLRRLLL : Test firstParameters firstBoxLLLRRLLL :=
  Tree.sound firstParameters firstTreeRootLLLRRLLL firstBoxLLLRRLLL (by decide +kernel)

private def firstTreeRootLLLRRLLR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        .prune
        .leaf)
      .prune)
    (.split 0
      (.split 1
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)
        (.split 2
          .leaf
          .leaf))
      (.split 1
        (.split 2
          (.split 0
            .leaf
            .leaf)
          .leaf)
        (.split 2
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLRRLLR : Test firstParameters firstBoxLLLRRLLR :=
  Tree.sound firstParameters firstTreeRootLLLRRLLR firstBoxLLLRRLLR (by decide +kernel)

private theorem firstTestRootLLLRRLL : Test firstParameters firstBoxLLLRRLL :=
  split_test (B := firstBoxLLLRRLL) 1 firstTestRootLLLRRLLL firstTestRootLLLRRLLR

private def firstTreeRootLLLRRLR : Tree :=
  (.split 1
    (.split 2
      .prune
      (.split 0
        (.split 1
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf)
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf))
        (.split 1
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf)
          (.split 2
            .leaf
            .leaf))))
    (.split 2
      .prune
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          .leaf)
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLRRLR : Test firstParameters firstBoxLLLRRLR :=
  Tree.sound firstParameters firstTreeRootLLLRRLR firstBoxLLLRRLR (by decide +kernel)

private theorem firstTestRootLLLRRL : Test firstParameters firstBoxLLLRRL :=
  split_test (B := firstBoxLLLRRL) 0 firstTestRootLLLRRLL firstTestRootLLLRRLR

private def firstTreeRootLLLRRR : Tree :=
  (.split 0
    (.split 1
      (.split 2
        (.split 0
          (.split 1
            (.split 2
              .leaf
              .leaf)
            .leaf)
          (.split 1
            .leaf
            .leaf))
        (.split 0
          (.split 1
            .leaf
            .leaf)
          .leaf))
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))
        (.split 0
          .leaf
          .leaf)))
    (.split 1
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))
        (.split 0
          .leaf
          .leaf))
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          .leaf)
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLLRRR : Test firstParameters firstBoxLLLRRR :=
  Tree.sound firstParameters firstTreeRootLLLRRR firstBoxLLLRRR (by decide +kernel)

private theorem firstTestRootLLLRR : Test firstParameters firstBoxLLLRR :=
  split_test (B := firstBoxLLLRR) 2 firstTestRootLLLRRL firstTestRootLLLRRR

private theorem firstTestRootLLLR : Test firstParameters firstBoxLLLR :=
  split_test (B := firstBoxLLLR) 1 firstTestRootLLLRL firstTestRootLLLRR

private theorem firstTestRootLLL : Test firstParameters firstBoxLLL :=
  split_test (B := firstBoxLLL) 0 firstTestRootLLLL firstTestRootLLLR

private def firstBoxLLRL : Box := (firstBoxLLR.bisect 0).1

private def firstBoxLLRR : Box := (firstBoxLLR.bisect 0).2

private def firstTreeRootLLRL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            .leaf
            .leaf)))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        .leaf
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLRL : Test firstParameters firstBoxLLRL :=
  Tree.sound firstParameters firstTreeRootLLRL firstBoxLLRL (by decide +kernel)

private def firstTreeRootLLRR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf))
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            .leaf
            .leaf)))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          .leaf)
        (.split 1
          (.split 2
            (.split 0
              .leaf
              .leaf)
            .leaf)
          .leaf))
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLLRR : Test firstParameters firstBoxLLRR :=
  Tree.sound firstParameters firstTreeRootLLRR firstBoxLLRR (by decide +kernel)

private theorem firstTestRootLLR : Test firstParameters firstBoxLLR :=
  split_test (B := firstBoxLLR) 0 firstTestRootLLRL firstTestRootLLRR

private theorem firstTestRootLL : Test firstParameters firstBoxLL :=
  split_test (B := firstBoxLL) 2 firstTestRootLLL firstTestRootLLR

private def firstBoxLRL : Box := (firstBoxLR.bisect 2).1

private def firstBoxLRR : Box := (firstBoxLR.bisect 2).2

private def firstBoxLRLL : Box := (firstBoxLRL.bisect 0).1

private def firstBoxLRLR : Box := (firstBoxLRL.bisect 0).2

private def firstBoxLRLLL : Box := (firstBoxLRLL.bisect 1).1

private def firstBoxLRLLR : Box := (firstBoxLRLL.bisect 1).2

private def firstBoxLRLLLL : Box := (firstBoxLRLLL.bisect 2).1

private def firstBoxLRLLLR : Box := (firstBoxLRLLL.bisect 2).2

private def firstTreeRootLRLLLL : Tree :=
  (.split 0
    (.split 1
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))
        (.split 0
          .leaf
          .leaf))
      (.split 2
        (.split 0
          .leaf
          .leaf)
        .leaf))
    (.split 1
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf))
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf)))
      (.split 2
        (.split 0
          .leaf
          .leaf)
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLRLLLL : Test firstParameters firstBoxLRLLLL :=
  Tree.sound firstParameters firstTreeRootLRLLLL firstBoxLRLLLL (by decide +kernel)

private def firstTreeRootLRLLLR : Tree :=
  (.split 0
    (.split 1
      .leaf
      .leaf)
    (.split 1
      (.split 2
        .leaf
        .leaf)
      .leaf))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLRLLLR : Test firstParameters firstBoxLRLLLR :=
  Tree.sound firstParameters firstTreeRootLRLLLR firstBoxLRLLLR (by decide +kernel)

private theorem firstTestRootLRLLL : Test firstParameters firstBoxLRLLL :=
  split_test (B := firstBoxLRLLL) 2 firstTestRootLRLLLL firstTestRootLRLLLR

private def firstTreeRootLRLLR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        .leaf
        .leaf)
      .leaf)
    .leaf)

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLRLLR : Test firstParameters firstBoxLRLLR :=
  Tree.sound firstParameters firstTreeRootLRLLR firstBoxLRLLR (by decide +kernel)

private theorem firstTestRootLRLL : Test firstParameters firstBoxLRLL :=
  split_test (B := firstBoxLRLL) 1 firstTestRootLRLLL firstTestRootLRLLR

private def firstTreeRootLRLR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          (.split 2
            (.split 0
              (.split 1
                .leaf
                .leaf)
              .leaf)
            (.split 0
              (.split 1
                .leaf
                .leaf)
              (.split 1
                .leaf
                .leaf)))
          .leaf)
        (.split 1
          (.split 2
            .leaf
            .leaf)
          .leaf))
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          .leaf)
        .leaf))
    .leaf)

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLRLR : Test firstParameters firstBoxLRLR :=
  Tree.sound firstParameters firstTreeRootLRLR firstBoxLRLR (by decide +kernel)

private theorem firstTestRootLRL : Test firstParameters firstBoxLRL :=
  split_test (B := firstBoxLRL) 0 firstTestRootLRLL firstTestRootLRLR

private def firstTreeRootLRR : Tree :=
  (.split 0
    (.split 1
      (.split 2
        .leaf
        .leaf)
      .leaf)
    (.split 1
      (.split 2
        .leaf
        .leaf)
      .leaf))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootLRR : Test firstParameters firstBoxLRR :=
  Tree.sound firstParameters firstTreeRootLRR firstBoxLRR (by decide +kernel)

private theorem firstTestRootLR : Test firstParameters firstBoxLR :=
  split_test (B := firstBoxLR) 2 firstTestRootLRL firstTestRootLRR

private theorem firstTestRootL : Test firstParameters firstBoxL :=
  split_test (B := firstBoxL) 1 firstTestRootLL firstTestRootLR

private def firstBoxRL : Box := (firstBoxR.bisect 1).1

private def firstBoxRR : Box := (firstBoxR.bisect 1).2

private def firstBoxRLL : Box := (firstBoxRL.bisect 2).1

private def firstBoxRLR : Box := (firstBoxRL.bisect 2).2

private def firstBoxRLLL : Box := (firstBoxRLL.bisect 0).1

private def firstBoxRLLR : Box := (firstBoxRLL.bisect 0).2

private def firstBoxRLLLL : Box := (firstBoxRLLL.bisect 1).1

private def firstBoxRLLLR : Box := (firstBoxRLLL.bisect 1).2

private def firstBoxRLLLLL : Box := (firstBoxRLLLL.bisect 2).1

private def firstBoxRLLLLR : Box := (firstBoxRLLLL.bisect 2).2

private def firstBoxRLLLLLL : Box := (firstBoxRLLLLL.bisect 0).1

private def firstBoxRLLLLLR : Box := (firstBoxRLLLLL.bisect 0).2

private def firstTreeRootRLLLLLL : Tree :=
  (.split 1
    (.split 2
      (.split 0
        .leaf
        .leaf)
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf)))
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        (.split 1
          .leaf
          .leaf))
      (.split 0
        (.split 1
          (.split 2
            .leaf
            .leaf)
          (.split 2
            .leaf
            .leaf))
        (.split 1
          .leaf
          .leaf))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootRLLLLLL : Test firstParameters firstBoxRLLLLLL :=
  Tree.sound firstParameters firstTreeRootRLLLLLL firstBoxRLLLLLL (by decide +kernel)

private def firstTreeRootRLLLLLR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        .leaf
        .leaf)
      (.split 0
        .leaf
        .leaf))
    (.split 2
      (.split 0
        .leaf
        .leaf)
      (.split 0
        (.split 1
          .leaf
          .leaf)
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootRLLLLLR : Test firstParameters firstBoxRLLLLLR :=
  Tree.sound firstParameters firstTreeRootRLLLLLR firstBoxRLLLLLR (by decide +kernel)

private theorem firstTestRootRLLLLL : Test firstParameters firstBoxRLLLLL :=
  split_test (B := firstBoxRLLLLL) 0 firstTestRootRLLLLLL firstTestRootRLLLLLR

private def firstTreeRootRLLLLR : Tree :=
  (.split 0
    (.split 1
      (.split 2
        (.split 0
          .leaf
          .leaf)
        .leaf)
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          .leaf)
        (.split 0
          .leaf
          .leaf)))
    (.split 1
      (.split 2
        .leaf
        .leaf)
      (.split 2
        .leaf
        .leaf)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootRLLLLR : Test firstParameters firstBoxRLLLLR :=
  Tree.sound firstParameters firstTreeRootRLLLLR firstBoxRLLLLR (by decide +kernel)

private theorem firstTestRootRLLLL : Test firstParameters firstBoxRLLLL :=
  split_test (B := firstBoxRLLLL) 2 firstTestRootRLLLLL firstTestRootRLLLLR

private def firstTreeRootRLLLR : Tree :=
  (.split 2
    (.split 0
      (.split 1
        (.split 2
          (.split 0
            .prune
            .leaf)
          (.split 0
            (.split 1
              (.split 2
                .leaf
                .leaf)
              .leaf)
            (.split 1
              .leaf
              .leaf)))
        (.split 2
          .prune
          (.split 0
            .leaf
            .leaf)))
      (.split 1
        (.split 2
          .leaf
          .leaf)
        .leaf))
    (.split 0
      (.split 1
        (.split 2
          (.split 0
            (.split 1
              .leaf
              .leaf)
            .leaf)
          .leaf)
        .leaf)
      .leaf))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootRLLLR : Test firstParameters firstBoxRLLLR :=
  Tree.sound firstParameters firstTreeRootRLLLR firstBoxRLLLR (by decide +kernel)

private theorem firstTestRootRLLL : Test firstParameters firstBoxRLLL :=
  split_test (B := firstBoxRLLL) 1 firstTestRootRLLLL firstTestRootRLLLR

private def firstTreeRootRLLR : Tree :=
  (.split 1
    (.split 2
      (.split 0
        (.split 1
          .leaf
          .leaf)
        .leaf)
      (.split 0
        .leaf
        .leaf))
    .leaf)

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootRLLR : Test firstParameters firstBoxRLLR :=
  Tree.sound firstParameters firstTreeRootRLLR firstBoxRLLR (by decide +kernel)

private theorem firstTestRootRLL : Test firstParameters firstBoxRLL :=
  split_test (B := firstBoxRLL) 0 firstTestRootRLLL firstTestRootRLLR

private def firstTreeRootRLR : Tree :=
  (.split 0
    (.split 1
      (.split 2
        (.split 0
          (.split 1
            .leaf
            (.split 2
              .leaf
              .leaf))
          (.split 1
            .leaf
            .leaf))
        (.split 0
          (.split 1
            .leaf
            .leaf)
          (.split 1
            .leaf
            .leaf)))
      (.split 2
        (.split 0
          (.split 1
            .leaf
            .leaf)
          .leaf)
        (.split 0
          (.split 1
            .leaf
            .leaf)
          .leaf)))
    (.split 1
      (.split 2
        .leaf
        .leaf)
      .leaf))

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootRLR : Test firstParameters firstBoxRLR :=
  Tree.sound firstParameters firstTreeRootRLR firstBoxRLR (by decide +kernel)

private theorem firstTestRootRL : Test firstParameters firstBoxRL :=
  split_test (B := firstBoxRL) 2 firstTestRootRLL firstTestRootRLR

private def firstTreeRootRR : Tree :=
  .leaf

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem firstTestRootRR : Test firstParameters firstBoxRR :=
  Tree.sound firstParameters firstTreeRootRR firstBoxRR (by decide +kernel)

private theorem firstTestRootR : Test firstParameters firstBoxR :=
  split_test (B := firstBoxR) 1 firstTestRootRL firstTestRootRR

private theorem firstTestRoot : Test firstParameters firstBox :=
  split_test (B := firstBox) 0 firstTestRootL firstTestRootR

theorem first_test : HotBoxTest (1/2000) firstLimit firstHeight (1/2)
    (ShapeBox.root firstHeight) := by
  simpa only [firstBox, Test, Box.root_cast, firstParameters, firstLimit, firstHeight,
    Parameters.margin, Parameters.limit, Parameters.height, Parameters.loss,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using firstTestRoot

/-- The outer spectral margin, with the finite cover discharged. -/
theorem first_outer {r m n q : ℝ}
    (hr : 1 ≤ r) (hrT : r ≤ 1+firstLimit)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq : q ≤ 1)
    (houter : InOuterRegion firstHeight m n q) (U : unitary Mat) :
    (1-m)^2/2000 < normalizedDeficit r U m n q :=
  first_outer_normalizedDeficit first_test hr hrT hm hmn hnq hq houter U

private theorem first_exp_upper : Real.exp (7/150 : ℝ) ≤ 1 + firstLimit := by
  have h :=
    Real.exp_bound_div_one_sub_of_interval (x := 7/150) (by norm_num) (by norm_num)
  exact h.trans (by norm_num [firstLimit])

/-- The outer spectral margin in the original inverse temperature. -/
theorem first_outer_beta {β m n q : ℝ}
    (hβ : 0 ≤ β) (hβmax : β ≤ 7/50)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq : q ≤ 1)
    (houter : InOuterRegion firstHeight m n q) (U : unitary Mat) :
    (1-m)^2/2000 < normalizedDeficit (Real.exp (β/3)) U m n q :=
  first_outer (Real.one_le_exp (by positivity))
    ((Real.exp_le_exp_of_le (by linarith only [hβmax])).trans first_exp_upper)
    hm hmn hnq hq houter U

#print axioms first_outer_beta

end D5.S3.Quantum.Semigroups.WuCubicHotOuterFinite
