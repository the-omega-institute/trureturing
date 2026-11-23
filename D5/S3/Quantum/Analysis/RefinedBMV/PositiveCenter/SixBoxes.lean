/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/SixBoxes
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dyadic Taylor evaluation of the six small-corner boxes. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CornerEnclosures
import Batteries.Tactic.OpenPrivate

/-! Dyadic evaluation of the small-corner cover. -/

namespace RefinedBMV.PositiveCenter.SmallCorner

open Filter Set
open scoped Topology

set_option autoImplicit false

open private Bounds point add neg grid down up down_le le_up mul
  encloses_point encloses_add encloses_neg encloses_sub encloses_mul grid_pos jet_add
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CornerEnclosures

private abbrev DyadicInterval := ℤ × ℤ

private def gridInt : ℤ := 17592186044416

private def gridValue (n : ℤ) : ℚ := (n : ℚ) / grid

private def dyadicBounds (a : DyadicInterval) : Bounds :=
  (gridValue a.1, gridValue a.2)

private def dyadicPoint (n : ℤ) : DyadicInterval := (gridInt * n, gridInt * n)

private def dyadicNeg (a : DyadicInterval) : DyadicInterval := (-a.2, -a.1)

private def dyadicAdd (a b : DyadicInterval) : DyadicInterval := (a.1 + b.1, a.2 + b.2)

private def dyadicMul (a b : DyadicInterval) : DyadicInterval :=
  let p := a.1 * b.1
  let q := a.1 * b.2
  let r := a.2 * b.1
  let s := a.2 * b.2
  (min (min p q) (min r s) / gridInt, -(-max (max p q) (max r s) / gridInt))

private local instance : Add DyadicInterval := ⟨dyadicAdd⟩
private local instance : Mul DyadicInterval := ⟨dyadicMul⟩

private theorem dyadicPoint_bounds (n : ℤ) :
    dyadicBounds (dyadicPoint n) = point (n : ℚ) := by
  have h : (gridInt : ℚ) = grid := rfl
  simp [dyadicBounds, dyadicPoint, gridValue, h, grid_pos.ne', point]

private theorem dyadicNeg_bounds (a : DyadicInterval) :
    dyadicBounds (dyadicNeg a) = neg (dyadicBounds a) := by
  simp [dyadicBounds, dyadicNeg, neg, gridValue, neg_div]

private theorem dyadicAdd_bounds (a b : DyadicInterval) :
    dyadicBounds (dyadicAdd a b) = add (dyadicBounds a) (dyadicBounds b) := by
  simp [dyadicBounds, dyadicAdd, add, gridValue, add_div]

private theorem gridValue_mul (m n : ℤ) :
    gridValue m * gridValue n = ((m * n : ℤ) : ℚ) / grid ^ 2 := by
  simp only [gridValue, Int.cast_mul, div_mul_div_comm, pow_two]

private theorem down_gridProduct (n : ℤ) :
    down ((n : ℚ) / grid ^ 2) = gridValue (n / gridInt) := by
  have hcancel : (n : ℚ) / grid ^ 2 * grid = (n : ℚ) / grid := by
    field_simp [grid_pos.ne']
  rw [down, hcancel]
  change (⌊(n : ℚ) / ((17592186044416 : ℕ) : ℚ)⌋ : ℚ) / grid = _
  rw [Rat.floor_intCast_div_natCast]
  rfl

private theorem up_gridProduct (n : ℤ) :
    up ((n : ℚ) / grid ^ 2) = gridValue (-(-n / gridInt)) := by
  rw [up, ← neg_div, ← Int.cast_neg, down_gridProduct]
  simp [gridValue, neg_div]

private theorem dyadicMul_bounds (a b : DyadicInterval) :
    dyadicBounds (dyadicMul a b) = mul (dyadicBounds a) (dyadicBounds b) := by
  simp only [dyadicBounds, dyadicMul, mul, gridValue_mul,
    min_div_div_right (sq_nonneg grid), max_div_div_right (sq_nonneg grid),
    ← Int.cast_min, ← Int.cast_max, down_gridProduct, up_gridProduct]

private theorem dyadicPoint_encloses (n : ℤ) :
    Encloses (dyadicBounds (dyadicPoint n)) (n : ℝ) := by
  rw [dyadicPoint_bounds]
  simpa only [Rat.cast_intCast] using encloses_point (n : ℚ)

private theorem dyadicAdd_encloses {a b : DyadicInterval} {x y : ℝ}
    (hx : Encloses (dyadicBounds a) x) (hy : Encloses (dyadicBounds b) y) :
    Encloses (dyadicBounds (dyadicAdd a b)) (x + y) := by
  rw [dyadicAdd_bounds]
  exact encloses_add hx hy

private theorem dyadicMul_encloses {a b : DyadicInterval} {x y : ℝ}
    (hx : Encloses (dyadicBounds a) x) (hy : Encloses (dyadicBounds b) y) :
    Encloses (dyadicBounds (dyadicMul a b)) (x * y) := by
  rw [dyadicMul_bounds]
  exact encloses_mul hx hy

private def dyadicScalar (a : DyadicInterval) : MixedJet DyadicInterval :=
  ⟨a, dyadicPoint 0, dyadicPoint 0, dyadicPoint 0⟩

private def dyadicJet (a : MixedJet DyadicInterval) : MixedJet Bounds :=
  ⟨dyadicBounds a.value, dyadicBounds a.du, dyadicBounds a.dv, dyadicBounds a.duv⟩

private theorem dyadicScalar_encloses {a : DyadicInterval} {x : ℝ}
    (hx : Encloses (dyadicBounds a) x) :
    JetEncloses (dyadicJet (dyadicScalar a)) ⟨x, 0, 0, 0⟩ := by
  have hz : Encloses (dyadicBounds (dyadicPoint 0)) (0 : ℝ) := by
    simpa using dyadicPoint_encloses 0
  exact ⟨hx, hz, hz, hz⟩

private theorem dyadicJet_add (a b : MixedJet DyadicInterval) :
    dyadicJet (a.add b) = (dyadicJet a).add (dyadicJet b) := by
  change (⟨dyadicBounds (dyadicAdd a.value b.value), dyadicBounds (dyadicAdd a.du b.du),
    dyadicBounds (dyadicAdd a.dv b.dv), dyadicBounds (dyadicAdd a.duv b.duv)⟩ : MixedJet Bounds) = _
  simp only [dyadicAdd_bounds]
  rfl

private theorem dyadicJet_mul {a b : MixedJet DyadicInterval} {x y : MixedJet ℝ}
    (hx : JetEncloses (dyadicJet a) x) (hy : JetEncloses (dyadicJet b) y) :
    JetEncloses (dyadicJet (a.mul b)) (x.mul y) := by
  exact ⟨dyadicMul_encloses hx.1 hy.1,
    dyadicAdd_encloses (dyadicMul_encloses hx.2.1 hy.1) (dyadicMul_encloses hx.1 hy.2.1),
    dyadicAdd_encloses (dyadicMul_encloses hx.2.2.1 hy.1) (dyadicMul_encloses hx.1 hy.2.2.1),
    dyadicAdd_encloses (dyadicAdd_encloses (dyadicAdd_encloses
      (dyadicMul_encloses hx.2.2.2 hy.1) (dyadicMul_encloses hx.2.1 hy.2.2.1))
      (dyadicMul_encloses hx.2.2.1 hy.2.1)) (dyadicMul_encloses hx.1 hy.2.2.2)⟩

private theorem dyadicJet_add_sound {a b : MixedJet DyadicInterval} {x y : MixedJet ℝ}
    (hx : JetEncloses (dyadicJet a) x) (hy : JetEncloses (dyadicJet b) y) :
    JetEncloses (dyadicJet (a.add b)) (x.add y) :=
  by rw [dyadicJet_add]; exact jet_add hx hy

/-- Integer endpoints of the six leaves on the common dyadic grid. -/
private def dyadicSixBox (i : Fin 6) :
    DyadicInterval × DyadicInterval × DyadicInterval :=
  ![
    ((0, 4398046511104), (0, 8796093022208), (0, 4810363371520)),
    ((4398046511104, 8796093022208), (0, 4398046511104), (0, 4810363371520)),
    ((4398046511104, 6597069766656), (4398046511104, 8796093022208), (0, 4810363371520)),
    ((6597069766656, 8796093022208), (4398046511104, 6597069766656), (0, 4810363371520)),
    ((6597069766656, 8796093022208), (6597069766656, 8796093022208), (0, 2405181685760)),
    ((6597069766656, 8796093022208), (6597069766656, 8796093022208), (2405181685760, 4810363371520))
  ] i

private theorem dyadicSixBox_bounds (i : Fin 6) :
    (dyadicBounds (dyadicSixBox i).1, dyadicBounds (dyadicSixBox i).2.1,
      dyadicBounds (dyadicSixBox i).2.2) = sixBox i := by
  fin_cases i <;> decide +kernel

private def momentBoxIndex (i : Fin 6) : Fin 3 :=
  if i.val = 4 then 1 else if i.val = 5 then 2 else 0

private def momentBox (j : Fin 3) : DyadicInterval :=
  ![(0, 4810363371520), (0, 2405181685760), (2405181685760, 4810363371520)] j

private theorem momentBox_eq (i : Fin 6) :
    momentBox (momentBoxIndex i) = (dyadicSixBox i).2.2 := by
  fin_cases i <;> decide +kernel

private def exactDegreeBounds (j : Fin 3) : Array (Array DyadicInterval) :=
  ![
    #[
      #[(0, 0), (0, 0), (17592186044416, 17592186044416), (2345624805922, 2666315697358), (1759218604441, 2240254941595), (335089257988, 478791705435), (108205906225, 171817652759), (20943078624, 37347467604), (4537667035, 8977664044), (789772661, 1738312394), (134860733, 327838261), (20476592, 54977426), (2946214, 8731748)],
      #[],
      #[(17592186044416, 17592186044416), (-3999473546037, -3518437208883), (5277655813324, 6720764824782), (335089257988, 478791705435), (554991583544, 878076024463), (94243853809, 168063604211), (35952284971, 70859706237), (6917562333, 15215268328), (1594529849, 3865842910), (282265074, 756328967), (49753081, 146904939)],
      #[(2345624805922, 2666315697358), (-4480509883189, -3518437208883), (335089257988, 478791705435), (-897063785139, -568953635960), (-93368669006, -52357696560), (-86891822107, -44329516421), (-16748878888, -7626242266), (-5628223844, -2332297392), (-1137801192, -425533415), (-254278618, -86723630)],
      #[(1759218604441, 2240254941595), (-1196979263587, -837723144972), (554991583544, 878076024463), (-93368669006, -52357696560), (48518132146, 94907880042), (3077997919, 6748547741), (2641683781, 6338873789), (388919641, 1037656912), (108809742, 317150431)],
      #[(335089257988, 478791705435), (-515452958272, -324617718676), (94243853809, 168063604211), (-86891822107, -44329516421), (3077997919, 6748547741), (-6202441371, -2594085875), (-436449650, -163744932), (-316708770, -109347326)],
      #[(108205906225, 171817652759), (-130716136609, -73300775185), (35952284971, 70859706237), (-16748878888, -7626242266), (2641683781, 6338873789), (-436449650, -163744932), (107424618, 310220985)],
      #[(20943078624, 37347467604), (-35910656173, -18150668141), (6917562333, 15215268328), (-5628223844, -2332297392), (388919641, 1037656912), (-316708770, -109347326)],
      #[(4537667035, 8977664044), (-7822405770, -3553976978), (1594529849, 3865842910), (-1137801192, -425533415), (108809742, 317150431)],
      #[(789772661, 1738312394), (-1639191300, -674303667), (282265074, 756328967), (-254278618, -86723630)],
      #[(134860733, 327838261), (-302375835, -112621256), (49753081, 146904939)],
      #[(20476592, 54977426), (-52390482, -17677284)],
      #[(2946214, 8731748)]
    ],
    #[
      #[(0, 0), (0, 0), (17592186044416, 17592186044416), (2345624805922, 2505970251641), (1759218604441, 1999736773019), (335089257988, 405374608219), (108205906225, 138902619101), (20943078624, 28623315283), (4537667035, 6578242536), (789772661, 1215866875), (134860733, 219981098), (20476592, 35393476), (2946214, 5392724)],
      #[],
      #[(17592186044416, 17592186044416), (-3758955377461, -3518437208883), (5277655813324, 5999210319054), (335089257988, 405374608219), (554991583544, 711640449338), (94243853809, 128804918771), (35952284971, 52052167480), (6917562333, 10647069665), (1594529849, 2598362371), (282265074, 487603359), (49753081, 90966145)],
      #[(2345624805922, 2505970251641), (-3999473546037, -3518437208883), (335089257988, 405374608219), (-728767803172, -568953635960), (-71558288206, -52357696560), (-64061106953, -44329516421), (-11731539465, -7626242266), (-3794016574, -2332297392), (-734501753, -425533415), (-158230976, -86723630)],
      #[(1759218604441, 1999736773019), (-1013436520547, -837723144972), (554991583544, 711640449338), (-71558288206, -52357696560), (48518132146, 70065576690), (3077997919, 4732070425), (2641683781, 4288316693), (388919641, 670742326), (108809742, 198085746)],
      #[(335089257988, 405374608219), (-416707857302, -324617718676), (94243853809, 128804918771), (-64061106953, -44329516421), (3077997919, 4732070425), (-4205495107, -2594085875), (-282291868, -163744932), (-198562263, -109347326)],
      #[(108205906225, 138902619101), (-100181603489, -73300775185), (35952284971, 52052167480), (-11731539465, -7626242266), (2641683781, 4288316693), (-282291868, -163744932), (107424618, 194841110)],
      #[(20943078624, 28623315283), (-26312970140, -18150668141), (6917562333, 10647069665), (-3794016574, -2332297392), (388919641, 670742326), (-198562263, -109347326)],
      #[(4537667035, 6578242536), (-5471400935, -3553976978), (1594529849, 2598362371), (-734501753, -425533415), (108809742, 198085746)],
      #[(789772661, 1215866875), (-1099905486, -674303667), (282265074, 487603359), (-158230976, -86723630)],
      #[(134860733, 219981098), (-194664110, -112621256), (49753081, 90966145)],
      #[(20476592, 35393476), (-32356336, -17677284)],
      #[(2946214, 5392724)]
    ],
    #[
      #[(0, 0), (0, 0), (17592186044416, 17592186044416), (2505970251639, 2666315697358), (1988775658563, 2229293827141), (405160523950, 478363536902), (138657732343, 171337635692), (28564207126, 37235105159), (6557001171, 8938849104), (1212031074, 1732146861), (219199259, 326750554), (35284574, 54834663), (5373621, 8680906)],
      #[],
      #[(17592186044416, 17592186044416), (-3999473546037, -3758955377458), (5966326975691, 6687881481422), (405160523950, 478363536902), (710178446135, 875225191397), (128538932068, 167557973211), (51847966526, 70479969590), (10611579996, 15157621837), (2586893309, 3848719581), (485985886, 754718611), (90601740, 146149770)],
      #[(2505970251639, 2666315697358), (-4458587654282, -3977551317128), (405160523950, 478363536902), (-893762204339, -727068230548), (-93087762895, -71410517815), (-86296021337, -63745883175), (-16676592356, -11687877399), (-5592361729, -3771595436), (-1134303957, -731447773), (-253414875, -157448334)],
      #[(1988775658563, 2229293827141), (-1195908842254, -1012901309878), (710178446135, 875225191397), (-93087762895, -71410517815), (69694841500, 94204047209), (4712390630, 6715411102), (4255201971, 6283465159), (667346647, 1033344001), (196623728, 315370822)],
      #[(405160523950, 478363536902), (-514012907072, -415973197033), (128538932068, 167557973211), (-86296021337, -63745883175), (4712390630, 6715411102), (-6138891044, -4168206348), (-434420008, -280746460), (-313794813, -196477357)],
      #[(138657732343, 171337635692), (-130322868054, -99974724942), (51847966526, 70479969590), (-16676592356, -11687877399), (4255201971, 6283465159), (-434420008, -280746460), (192512517, 306844984)],
      #[(28564207126, 37235105159), (-35755396411, -26228004687), (10611579996, 15157621837), (-5592361729, -3771595436), (667346647, 1033344001), (-313794813, -196477357)],
      #[(6557001171, 8938849104), (-7794660873, -5454139839), (2586893309, 3848719581), (-1134303957, -731447773), (196623728, 315370822)],
      #[(1212031074, 1732146861), (-1633752767, -1095996299), (485985886, 754718611), (-253414875, -157448334)],
      #[(219199259, 326750554), (-301590640, -194065162), (90601740, 146149770)],
      #[(35284574, 54834663), (-52085425, -32241727)],
      #[(5373621, 8680906)]
    ]
  ] j


private def dyadicFraction (n : ℤ) (d : ℕ) : DyadicInterval :=
  (n * gridInt / (d : ℤ), -((-n) * gridInt / (d : ℤ)))

private theorem dyadicFraction_bounds (n : ℤ) (d : ℕ) :
    dyadicBounds (dyadicFraction n d) =
      (down ((n : ℚ) / (d : ℚ)), up ((n : ℚ) / (d : ℚ))) := by
  have hf (m : ℤ) : ⌊((m : ℚ) / (d : ℚ)) * grid⌋ = m * gridInt / (d : ℤ) := by
    rw [div_mul_eq_mul_div, ← show (gridInt : ℚ) = grid by rfl, ← Int.cast_mul,
      Rat.floor_intCast_div_natCast]
  simp only [dyadicBounds, dyadicFraction, down, up, hf, gridValue,
    ← neg_div, ← Int.cast_neg]

private theorem dyadicFraction_encloses (n : ℤ) (d : ℕ) :
    Encloses (dyadicBounds (dyadicFraction n d)) ((n : ℝ) / (d : ℝ)) := by
  rw [dyadicFraction_bounds]
  simpa only [Encloses, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
    And.intro (Rat.cast_le (K := ℝ).mpr (down_le ((n : ℚ) / (d : ℚ))))
      (Rat.cast_le (K := ℝ).mpr (le_up ((n : ℚ) / (d : ℚ))))

private def dyadicHorner (h : DyadicInterval) (denom : ℕ) : List ℤ → DyadicInterval
  | [] => dyadicPoint 0
  | c :: cs => dyadicAdd (dyadicMul (dyadicHorner h denom cs) h) (dyadicFraction c denom)

private theorem dyadicHorner_encloses {hbox : DyadicInterval} {h : ℝ}
    (hh : Encloses (dyadicBounds hbox) h) (denom : ℕ) (cs : List ℤ) :
    Encloses (dyadicBounds (dyadicHorner hbox denom cs))
      (momentHorner h (cs.map fun (c : ℤ) ↦ (c : ℚ) / (denom : ℚ))) := by
  induction cs with
  | nil => simpa [dyadicHorner, momentHorner] using dyadicPoint_encloses 0
  | cons c cs ih =>
    simpa only [List.map_cons, dyadicHorner, momentHorner, Rat.cast_div, Rat.cast_intCast,
      Rat.cast_natCast, mul_comm, add_comm] using
      dyadicAdd_encloses (dyadicMul_encloses ih hh) (dyadicFraction_encloses c denom)

private def exactDegreeBound (i : Fin 6) (a b : ℕ) : DyadicInterval :=
  ((exactDegreeBounds (momentBoxIndex i)).getD a #[]).getD b (0, 0)

private def coarseDegreeBound (a b : ℕ) : DyadicInterval :=
  let d := a.factorial * b.factorial
  let n : ℤ := 2 ^ (a+b-1)
  ((dyadicFraction (-n) d).1, (dyadicFraction n d).2)

private def coefficientBound (i : Fin 6) (a b : ℕ) : DyadicInterval :=
  if a+b ≤ 12 then exactDegreeBound i a b else coarseDegreeBound a b

private def dyadicContained (outer inner : DyadicInterval) : Prop :=
  outer.1 ≤ inner.1 ∧ inner.2 ≤ outer.2

private instance (outer inner : DyadicInterval) : Decidable (dyadicContained outer inner) :=
  inferInstanceAs (Decidable (_ ≤ _ ∧ _ ≤ _))

private theorem dyadicContained_encloses {outer inner : DyadicInterval} {x : ℝ}
    (hc : dyadicContained outer inner) (hx : Encloses (dyadicBounds inner) x) :
    Encloses (dyadicBounds outer) x := by
  have h₁ : (gridValue outer.1 : ℝ) ≤ (gridValue inner.1 : ℝ) :=
    Rat.cast_le.mpr (div_le_div_of_nonneg_right (by exact_mod_cast hc.1) grid_pos.le)
  have h₂ : (gridValue inner.2 : ℝ) ≤ (gridValue outer.2 : ℝ) :=
    Rat.cast_le.mpr (div_le_div_of_nonneg_right (by exact_mod_cast hc.2) grid_pos.le)
  exact ⟨h₁.trans hx.1, hx.2.trans h₂⟩

private theorem coarseDegreeBound_encloses {p a b : ℕ} (hp : 0 < p)
    (hab : 2 ≤ a+b) (ha : a = 0 ∨ 2 ≤ a) :
    Encloses (dyadicBounds (coarseDegreeBound a b))
      (momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs a b)) := by
  have hc : |momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs a b)| ≤
      (2 : ℝ) ^ (a+b-1) / ((a.factorial : ℝ) * (b.factorial : ℝ)) := by
    rcases ha with rfl | ha
    · obtain ⟨r, rfl⟩ : ∃ r, b = r+2 := ⟨b-2, by omega⟩
      simpa [show r+2-1 = r+1 by omega] using normalized_moment_abs_bound_marginal hp r
    · obtain ⟨r, rfl⟩ : ∃ r, a = r+2 := ⟨a-2, by omega⟩
      simpa [show r+2+b-1 = r+b+1 by omega] using normalized_moment_abs_bound_joint hp r b
  obtain ⟨hlo, hhi⟩ := abs_le.mp hc
  have hlo' := (dyadicFraction_encloses (-(2 : ℤ)^(a+b-1)) (a.factorial*b.factorial)).1
  have hhi' := (dyadicFraction_encloses ((2 : ℤ)^(a+b-1)) (a.factorial*b.factorial)).2
  refine ⟨hlo'.trans ?_, hhi.trans ?_⟩
  · simpa only [Int.cast_neg, Int.cast_pow, Int.cast_ofNat, Nat.cast_mul, neg_div] using hlo
  · push_cast at hhi'
    exact hhi'


private def checkExactDegreeBound (i : Fin 6) (a b : ℕ) : Prop :=
  dyadicContained (exactDegreeBound i a b)
    (dyadicHorner (dyadicSixBox i).2.2 (certifiedMomentDenominator a b)
      (stagedNumerators a b))

private def checkExactDegreeRow (j : Fin 3) (a : ℕ) : Bool :=
  (List.range (13-a)).all fun b ↦
    if 2 ≤ a+b ∧ (a = 0 ∨ 2 ≤ a) then
      decide (dyadicContained (((exactDegreeBounds j).getD a #[]).getD b (0, 0))
        (dyadicHorner (momentBox j) (certifiedMomentDenominator a b)
          (stagedNumerators a b)))
    else true

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
set_option cbv.maxSteps 5000000 in
private theorem exactDegreeRows_checked (j : Fin 3) :
    (List.range 13).all (checkExactDegreeRow j) = true := by
  fin_cases j <;> decide_cbv

private theorem exactDegreeBound_checked (i : Fin 6) {a b : ℕ}
    (hcut : a+b ≤ 12) (hab : 2 ≤ a+b) (ha : a = 0 ∨ 2 ≤ a) :
    checkExactDegreeBound i a b := by
  have hrow := List.all_eq_true.mp (exactDegreeRows_checked (momentBoxIndex i)) a
    (List.mem_range.mpr (by omega))
  have he := List.all_eq_true.mp hrow b (List.mem_range.mpr (by omega))
  simpa [hab, ha, checkExactDegreeBound, exactDegreeBound, momentBox_eq] using he

private theorem coefficientBound_encloses {p a b : ℕ} (hp : 0 < p) (i : Fin 6)
    (hh : Encloses (dyadicBounds (dyadicSixBox i).2.2) (3 / (p : ℝ)))
    (hab : 2 ≤ a+b) (ha : a = 0 ∨ 2 ≤ a) :
    Encloses (dyadicBounds (coefficientBound i a b))
      (momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs a b)) := by
  unfold coefficientBound
  split_ifs with hc
  · rw [← certifiedMomentCoeffs_eq, certifiedMomentCoeffs, ← stagedNumerators_eq hc hab ha]
    exact dyadicContained_encloses (exactDegreeBound_checked i hc hab ha)
      (dyadicHorner_encloses hh _ _)
  · exact coarseDegreeBound_encloses hp hab ha

private theorem cornerJetHorner_encloses {x : MixedJet DyadicInterval} {t : MixedJet ℝ}
    (ht : JetEncloses (dyadicJet x) t)
    {z : MixedJet DyadicInterval} {z' : MixedJet ℝ} (hz : JetEncloses (dyadicJet z) z')
    (c : ℕ → MixedJet DyadicInterval) (c' : ℕ → MixedJet ℝ)
    (hc : ∀ i, JetEncloses (dyadicJet (c i)) (c' i)) (n start : ℕ) :
    JetEncloses (dyadicJet (cornerJetHorner x z c start n)) (cornerJetHorner t z' c' start n) := by
  induction n generalizing start with
  | zero => exact hz
  | succ n ih =>
    exact dyadicJet_add_sound (dyadicJet_mul (ih (start+1)) ht) (hc start)

private theorem marginalHorner_encloses {x : MixedJet DyadicInterval} {t : MixedJet ℝ}
    (ht : JetEncloses (dyadicJet x) t)
    {z : MixedJet DyadicInterval} {z' : MixedJet ℝ} (hz : JetEncloses (dyadicJet z) z')
    {c : List (MixedJet DyadicInterval)} {c' : List (MixedJet ℝ)}
    (hc : List.Forall₂ (fun a b ↦ JetEncloses (dyadicJet a) b) c c') :
    JetEncloses (dyadicJet (marginalHorner MixedJet.add MixedJet.mul z x c))
      (marginalHorner MixedJet.add MixedJet.mul z' t c') := by
  induction hc with
  | nil => exact hz
  | cons h _ ih => exact dyadicJet_add_sound (dyadicJet_mul ih ht) h

private theorem marginalDifferenceHorner_encloses
    {v d : MixedJet DyadicInterval} {v' d' : MixedJet ℝ}
    (hv : JetEncloses (dyadicJet v) v') (hd : JetEncloses (dyadicJet d) d')
    {z : MixedJet DyadicInterval} {z' : MixedJet ℝ} (hz : JetEncloses (dyadicJet z) z')
    {c : List (MixedJet DyadicInterval)} {c' : List (MixedJet ℝ)}
    (hc : List.Forall₂ (fun a b ↦ JetEncloses (dyadicJet a) b) c c') :
    let r := marginalDifferenceHorner MixedJet.add MixedJet.mul z v d c
    let r' := marginalDifferenceHorner MixedJet.add MixedJet.mul z' v' d' c'
    JetEncloses (dyadicJet r.atV) r'.atV ∧ JetEncloses (dyadicJet r.atD) r'.atD ∧
    JetEncloses (dyadicJet r.prime) r'.prime ∧
    JetEncloses (dyadicJet r.firstDifference) r'.firstDifference ∧
    JetEncloses (dyadicJet r.secondDifference) r'.secondDifference := by
  induction hc with
  | nil => exact ⟨hz, hz, hz, hz, hz⟩
  | cons h _ ih =>
    rcases ih with ⟨hV, hD, hP, hF, hS⟩
    exact ⟨dyadicJet_add_sound (dyadicJet_mul hV hv) h,
      dyadicJet_add_sound (dyadicJet_mul hD hd) h,
      dyadicJet_add_sound (dyadicJet_mul hP hv) hV,
      dyadicJet_add_sound (dyadicJet_mul hF hv) hD,
      dyadicJet_add_sound (dyadicJet_mul hS hv) hF⟩

private def dyadicCornerBounds (c : CornerInputs DyadicInterval) : CornerInputs Bounds :=
  ⟨dyadicJet c.joint, dyadicJet c.prime, dyadicJet c.firstDifference,
    dyadicJet c.secondDifference, dyadicJet c.atV, dyadicJet c.atD,
    dyadicJet c.atNegU, dyadicJet c.atNegV⟩

private def dyadicTaylorReplay (i : Fin 6) : CornerInputs DyadicInterval :=
  let ub := (dyadicSixBox i).1
  let db := (dyadicSixBox i).2.1
  let vb := dyadicAdd ub db
  let z := dyadicPoint 0
  let one := dyadicPoint 1
  let negOne := dyadicPoint (-1)
  let u : MixedJet DyadicInterval := ⟨ub, one, z, z⟩
  let v : MixedJet DyadicInterval := ⟨vb, z, one, z⟩
  let d : MixedJet DyadicInterval := ⟨db, negOne, one, z⟩
  let negU : MixedJet DyadicInterval := ⟨dyadicNeg ub, negOne, z, z⟩
  let negV : MixedJet DyadicInterval := ⟨dyadicNeg vb, z, negOne, z⟩
  let zero := dyadicScalar z
  let cs := List.ofFn (n := 23) fun k ↦ dyadicScalar (coefficientBound i 0 (k.val+2))
  let result := marginalDifferenceHorner MixedJet.add MixedJet.mul zero v d cs
  ⟨cornerJointHorner u v zero (fun a b ↦ dyadicScalar (coefficientBound i (a+2) b)) 23,
    result.prime, result.firstDifference, result.secondDifference, result.atV, result.atD,
    marginalHorner MixedJet.add MixedJet.mul zero negU cs,
    marginalHorner MixedJet.add MixedJet.mul zero negV cs⟩


private theorem forall₂_ofFn {α β : Type} {n : ℕ}
    {P : α → β → Prop} {f : Fin n → α} {g : Fin n → β}
    (h : ∀ i, P (f i) (g i)) : List.Forall₂ P (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [List.ofFn_succ] using List.Forall₂.cons (h 0) (ih (fun i ↦ h i.succ))

private theorem dyadicTaylorReplay_encloses {p : ℕ} (hp : 0 < p) (i : Fin 6)
    {u d : ℝ} (hu : Encloses (sixBox i).1 u) (hd : Encloses (sixBox i).2.1 d)
    (hh : Encloses (sixBox i).2.2 (3 / (p : ℝ))) :
    CornerEncloses (dyadicCornerBounds (dyadicTaylorReplay i)) (taylorCornerInputs p u (u+d)) := by
  have hboxes := dyadicSixBox_bounds i
  have hU : Encloses (dyadicBounds (dyadicSixBox i).1) u := by
    have e : dyadicBounds (dyadicSixBox i).1 = (sixBox i).1 := congrArg Prod.fst hboxes
    rwa [e]
  have hD : Encloses (dyadicBounds (dyadicSixBox i).2.1) d := by
    have e : dyadicBounds (dyadicSixBox i).2.1 = (sixBox i).2.1 :=
      congrArg (fun b ↦ b.2.1) hboxes
    rwa [e]
  have hH : Encloses (dyadicBounds (dyadicSixBox i).2.2) (3 / (p : ℝ)) := by
    have e : dyadicBounds (dyadicSixBox i).2.2 = (sixBox i).2.2 :=
      congrArg (fun b ↦ b.2.2) hboxes
    rwa [e]
  let v := u+d
  let ub := (dyadicSixBox i).1
  let db := (dyadicSixBox i).2.1
  let vb := dyadicAdd ub db
  have hV : Encloses (dyadicBounds vb) v := dyadicAdd_encloses hU hD
  have hnU : Encloses (dyadicBounds (dyadicNeg ub)) (-u) := by
    rw [dyadicNeg_bounds]
    exact encloses_neg hU
  have hnV : Encloses (dyadicBounds (dyadicNeg vb)) (-v) := by
    rw [dyadicNeg_bounds]
    exact encloses_neg hV
  let z := dyadicPoint 0
  let one := dyadicPoint 1
  let negOne := dyadicPoint (-1)
  have hz : Encloses (dyadicBounds z) (0 : ℝ) := by simpa using dyadicPoint_encloses 0
  have h1 : Encloses (dyadicBounds one) (1 : ℝ) := by simpa using dyadicPoint_encloses 1
  have hn1 : Encloses (dyadicBounds negOne) (-1 : ℝ) := by simpa using dyadicPoint_encloses (-1)
  let uJet : MixedJet DyadicInterval := ⟨ub, one, z, z⟩
  let vJet : MixedJet DyadicInterval := ⟨vb, z, one, z⟩
  let dJet : MixedJet DyadicInterval := ⟨db, negOne, one, z⟩
  let nUJet : MixedJet DyadicInterval := ⟨dyadicNeg ub, negOne, z, z⟩
  let nVJet : MixedJet DyadicInterval := ⟨dyadicNeg vb, z, negOne, z⟩
  have hUj : JetEncloses (dyadicJet uJet) (⟨u, 1, 0, 0⟩ : MixedJet ℝ) := ⟨hU, h1, hz, hz⟩
  have hVj : JetEncloses (dyadicJet vJet) (⟨v, 0, 1, 0⟩ : MixedJet ℝ) := ⟨hV, hz, h1, hz⟩
  have hDj : JetEncloses (dyadicJet dJet) (marginalAffineInput (-1) 1 u v) := by
    simpa [marginalAffineInput, v] using
      (show JetEncloses (dyadicJet dJet) (⟨d, -1, 1, 0⟩ : MixedJet ℝ) from ⟨hD, hn1, h1, hz⟩)
  have hnUj : JetEncloses (dyadicJet nUJet) (marginalAffineInput (-1) 0 u v) := by
    simpa [marginalAffineInput] using
      (show JetEncloses (dyadicJet nUJet) (⟨-u, -1, 0, 0⟩ : MixedJet ℝ) from ⟨hnU, hn1, hz, hz⟩)
  have hnVj : JetEncloses (dyadicJet nVJet) (marginalAffineInput 0 (-1) u v) := by
    simpa [marginalAffineInput] using
      (show JetEncloses (dyadicJet nVJet) (⟨-v, 0, -1, 0⟩ : MixedJet ℝ) from ⟨hnV, hz, hn1, hz⟩)
  have hvAffine : JetEncloses (dyadicJet vJet) (marginalAffineInput 0 1 u v) := by
    simpa [marginalAffineInput] using hVj
  have hzero : JetEncloses (dyadicJet (dyadicScalar z)) (marginalScalarJet 0) :=
    dyadicScalar_encloses hz
  let cr (a b : ℕ) := momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs a b)
  have hc (a b : ℕ) (hab : 2 ≤ a+b) (ha : a = 0 ∨ 2 ≤ a) :
      JetEncloses (dyadicJet (dyadicScalar (coefficientBound i a b))) (marginalScalarJet (cr a b)) :=
    dyadicScalar_encloses (coefficientBound_encloses hp i hH hab ha)
  let cs := List.ofFn (n := 23) fun k ↦ dyadicScalar (coefficientBound i 0 (k.val+2))
  have hcs : List.Forall₂ (fun a b ↦ JetEncloses (dyadicJet a) b)
      cs ((marginalTaylorMomentCoefficients p).map marginalScalarJet) := by
    unfold cs marginalTaylorMomentCoefficients
    rw [List.map_ofFn]
    exact forall₂_ofFn (fun k ↦ hc 0 (k.val+2) (by omega) (Or.inl rfl))
  have hJ := cornerJetHorner_encloses hUj hzero
    (fun a ↦ cornerJetHorner vJet (dyadicScalar z)
      (fun b ↦ dyadicScalar (coefficientBound i (a+2) b)) 0 (23-a))
    (fun a ↦ cornerJetHorner (⟨v, 0, 1, 0⟩ : MixedJet ℝ) (marginalScalarJet 0)
      (fun b ↦ marginalScalarJet (cr (a+2) b)) 0 (23-a))
    (fun a ↦ cornerJetHorner_encloses hVj hzero _ _
      (fun b ↦ hc (a+2) b (by omega) (Or.inr (by omega))) (23-a) 0) 23 0
  have hJ' : JetEncloses (dyadicJet (dyadicTaylorReplay i).joint)
      (taylorCornerInputs p u v).joint := by
    rw [show (taylorCornerInputs p u v).joint = _ from
      jointTaylorPolynomial_jet_eq_cornerJointHorner hp u v]
    exact hJ
  have hM := marginalDifferenceHorner_encloses hvAffine hDj hzero hcs
  obtain ⟨eV, eD, eP, eF, eS⟩ := marginalDifferenceHorner_taylor hp u v
  rcases hM with ⟨hMv, hMd, hMp, hMf, hMs⟩
  rw [eV] at hMv
  rw [eD] at hMd
  rw [eP] at hMp
  rw [eF] at hMf
  rw [eS] at hMs
  have hNu := marginalHorner_encloses hnUj hzero hcs
  have hNv := marginalHorner_encloses hnVj hzero hcs
  rw [marginalHorner_affineTaylor hp] at hNu hNv
  exact ⟨hJ', hMp, hMf, hMs, hMv, hMd, hNu, hNv⟩

private def BoundsContained (outer inner : Bounds) : Prop :=
  outer.1 ≤ inner.1 ∧ inner.2 ≤ outer.2

private def JetContained (outer inner : MixedJet Bounds) : Prop :=
  BoundsContained outer.value inner.value ∧ BoundsContained outer.du inner.du ∧
  BoundsContained outer.dv inner.dv ∧ BoundsContained outer.duv inner.duv

private def CornerContained (outer inner : CornerInputs Bounds) : Prop :=
  JetContained outer.joint inner.joint ∧ JetContained outer.prime inner.prime ∧
  JetContained outer.firstDifference inner.firstDifference ∧
  JetContained outer.secondDifference inner.secondDifference ∧
  JetContained outer.atV inner.atV ∧ JetContained outer.atD inner.atD ∧
  JetContained outer.atNegU inner.atNegU ∧ JetContained outer.atNegV inner.atNegV

private instance (a b : Bounds) : Decidable (BoundsContained a b) :=
  inferInstanceAs (Decidable (_ ≤ _ ∧ _ ≤ _))

private instance (a b : MixedJet Bounds) : Decidable (JetContained a b) :=
  inferInstanceAs (Decidable (BoundsContained _ _ ∧ BoundsContained _ _ ∧
    BoundsContained _ _ ∧ BoundsContained _ _))

private instance (a b : CornerInputs Bounds) : Decidable (CornerContained a b) :=
  inferInstanceAs (Decidable (JetContained _ _ ∧ JetContained _ _ ∧ JetContained _ _ ∧
    JetContained _ _ ∧ JetContained _ _ ∧ JetContained _ _ ∧ JetContained _ _ ∧ JetContained _ _))

private theorem boundsContained_encloses {a b : Bounds} {x : ℝ}
    (hs : BoundsContained a b) (hx : Encloses b x) : Encloses a x :=
  ⟨(Rat.cast_le.mpr hs.1).trans hx.1, hx.2.trans (Rat.cast_le.mpr hs.2)⟩

private theorem jetContained_encloses {a b : MixedJet Bounds} {x : MixedJet ℝ}
    (hs : JetContained a b) (hx : JetEncloses b x) : JetEncloses a x :=
  ⟨boundsContained_encloses hs.1 hx.1, boundsContained_encloses hs.2.1 hx.2.1,
    boundsContained_encloses hs.2.2.1 hx.2.2.1, boundsContained_encloses hs.2.2.2 hx.2.2.2⟩

private theorem cornerContained_encloses {a b : CornerInputs Bounds} {x : CornerInputs ℝ}
    (hs : CornerContained a b) (hx : CornerEncloses b x) : CornerEncloses a x := by
  rcases hs with ⟨hJ, hP, hF, hS, hV, hD, hnU, hnV⟩
  rcases hx with ⟨eJ, eP, eF, eS, eV, eD, enU, enV⟩
  exact ⟨jetContained_encloses hJ eJ, jetContained_encloses hP eP, jetContained_encloses hF eF,
    jetContained_encloses hS eS, jetContained_encloses hV eV, jetContained_encloses hD eD,
    jetContained_encloses hnU enU, jetContained_encloses hnV enV⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
set_option cbv.maxSteps 5000000 in
private theorem dyadicTaylorReplay_checked (i : Fin 6) :
    CornerContained (taylorPrimitiveBounds i) (dyadicCornerBounds (dyadicTaylorReplay i)) := by
  fin_cases i <;> decide_cbv

/-- The original six leaves enclose every component of the Taylor jets. -/
theorem taylorBoxesEnclose : TaylorBoxesEnclose := by
  intro p hp i u d hu hd hh
  exact cornerContained_encloses (dyadicTaylorReplay_checked i)
    (dyadicTaylorReplay_encloses (by omega : 0 < p) i hu hd hh)

/-- For every natural degree at least eleven, the mixed derivative is uniformly
negative in the open ordered small corner. -/
theorem logKernel_small_corner_lt {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 0 < u) (hu₁ : u ≤ 1 / 2) (huv : u < v) (hd : v-u ≤ 1 / 2) :
    v^2 * deriv (fun t ↦ deriv (fun s ↦ logKernel p s t) u) v < -1/9 :=
  logKernel_small_corner_lt_of_taylorBoxes taylorBoxesEnclose hp hu hu₁ huv hd

#print axioms taylorBoxesEnclose
#print axioms logKernel_small_corner_lt

/-- The dyadic enclosure operations shared by the compact kernel certificates. -/
structure RoundedInterval where
  endpoints : ℤ × ℤ

namespace RoundedInterval

def lower (I : RoundedInterval) : ℚ := (dyadicBounds I.endpoints).1
def upper (I : RoundedInterval) : ℚ := (dyadicBounds I.endpoints).2
def encloses (I : RoundedInterval) (x : ℝ) : Prop := Encloses (dyadicBounds I.endpoints) x

def interval (lo hi : ℚ) : RoundedInterval :=
  ⟨(dyadicFraction lo.num lo.den).1, (dyadicFraction hi.num hi.den).2⟩

def point (q : ℚ) : RoundedInterval := interval q q

instance : Add RoundedInterval := ⟨fun a b ↦ ⟨dyadicAdd a.endpoints b.endpoints⟩⟩
instance : Sub RoundedInterval := ⟨fun a b ↦ ⟨dyadicAdd a.endpoints (dyadicNeg b.endpoints)⟩⟩
instance : Mul RoundedInterval := ⟨fun a b ↦ ⟨dyadicMul a.endpoints b.endpoints⟩⟩
instance : Zero RoundedInterval := ⟨point 0⟩

theorem encloses_interval {lo hi : ℚ} {x : ℝ} (hl : (lo : ℝ) ≤ x) (hu : x ≤ (hi : ℝ)) :
    (interval lo hi).encloses x := by
  have hc (q : ℚ) : (q.num : ℝ) / (q.den : ℝ) = (q : ℝ) := by
    exact_mod_cast q.num_div_den
  have hL := dyadicFraction_encloses lo.num lo.den
  have hU := dyadicFraction_encloses hi.num hi.den
  rw [hc] at hL hU
  exact ⟨hL.1.trans hl, hu.trans hU.2⟩

theorem encloses_point (q : ℚ) : (point q).encloses (q : ℝ) :=
  encloses_interval le_rfl le_rfl

theorem encloses_add {a b : RoundedInterval} {x y : ℝ} (ha : a.encloses x) (hb : b.encloses y) :
    (a + b).encloses (x + y) := dyadicAdd_encloses ha hb

theorem encloses_sub {a b : RoundedInterval} {x y : ℝ} (ha : a.encloses x) (hb : b.encloses y) :
    (a - b).encloses (x - y) := by
  rw [sub_eq_add_neg]
  refine dyadicAdd_encloses ha ?_
  rw [dyadicNeg_bounds]
  exact encloses_neg hb

theorem encloses_mul {a b : RoundedInterval} {x y : ℝ} (ha : a.encloses x) (hb : b.encloses y) :
    (a * b).encloses (x * y) := dyadicMul_encloses ha hb

end RoundedInterval

end RefinedBMV.PositiveCenter.SmallCorner
