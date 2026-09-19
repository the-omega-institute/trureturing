/- GID: D5/S3/Weil/Separator/TranslationEnergy/Generic/CellCertificate
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/Generic/CellCertificate
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate.full_certificate; instance=D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate
   digest: Certify exact coefficient provenance and signed interval arithmetic in every generic cell. -/

import D5.S3.Weil.Separator.TranslationEnergy.Integral
import D5.S3.Weil.Separator.TranslationEnergy.Polynomial.HornerIntervals
import D5.S3.Weil.Separator.TranslationEnergy.SignedSquares
import D5.S3.Weil.Separator.TranslationEnergy.CutoffIntervals
import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.TranslationEnergy.Generic

open _root_.Polynomial
open D5.S3.Weil.Separator.TranslationEnergy
open D5.S0.Certificates.BoxCover.RationalIntervalExpression
open D5.S3.Weil.Separator.TranslationEnergy.Polynomial
open D5.S3.Weil.Separator.TranslationEnergy.SignedSquares
open D5.S3.Weil.Separator.TranslationEnergy.CutoffIntervals
open D5.S3.Weil.Separator.TranslationEnergy.Scalar.Uniform

def normalizeCoefficients (cs : List Rat) : List Rat :=
  if cs = [] then [0] else cs

def productBounds (x y : Rat × Rat) : Rat × Rat :=
  (productLower x.1 x.2 y.1 y.2, productUpper x.1 x.2 y.1 y.2)

def genericCanonicalCellPayload (R : Nat) (a b s : Rat) (m : Nat)
    (pcs qcs : List Rat) : CanonicalCellPayload :=
  let ph := hornerInterval a b (evenizedCoefficients (normalizeCoefficients pcs))
  let qh := hornerInterval a b (evenizedCoefficients (normalizeCoefficients qcs))
  let ps := hornerInterval (a - s) (b - s)
    (evenizedCoefficients (normalizeCoefficients pcs))
  let qs := hornerInterval (a - s) (b - s)
    (evenizedCoefficients (normalizeCoefficients qcs))
  let w := cutoffCellBox R a b m (4 * m + 4)
  let ws := cutoffCellBox R (a - s) (b - s) m (4 * m + 4)
  let rh := productBounds w (bounds ph)
  let rs := productBounds ws (bounds ps)
  let ih := productBounds w (bounds qh)
  let is := productBounds ws (bounds qs)
  let rd := differenceBounds rh rs
  let id := differenceBounds ih is
  { pHere := ph
    qHere := qh
    pShift := ps
    qShift := qs
    norm := {
      reHere := rh
      reShift := rs
      reDiff := rd
      reSquare := squareBounds rd.1 rd.2
      imHere := ih
      imShift := is
      imDiff := id
      imSquare := squareBounds id.1 id.2
      total := normSqBounds rd id } }

def genericPayloads (R : Nat) (s : Rat) (d m : Nat) (pcs qcs : List Rat) :
    List CanonicalCellPayload :=
  (sourceCells R s d).map fun ab =>
    genericCanonicalCellPayload R ab.1 ab.2 s m pcs qcs

def coordinateBudget (R : Nat) (s : Rat) : Rat := 2 * R + |s| + 1

def linearBudget (R : Nat) (s : Rat) (pcs qcs : List Rat) : Rat :=
  let B := coordinateBudget R s
  let p := evenizedCoefficients (normalizeCoefficients pcs)
  let q := evenizedCoefficients (normalizeCoefficients qcs)
  let Ap := amplitude B p
  let Aq := amplitude B q
  4 * Ap * (18 * Ap / R + 2 * slope B p) +
    4 * Aq * (18 * Aq / R + 2 * slope B q)

def scalarBudget (R : Nat) (s : Rat) (pcs qcs : List Rat) : Rat :=
  let B := coordinateBudget R s
  16 * ((amplitude B (evenizedCoefficients (normalizeCoefficients pcs))) ^ 2 +
    (amplitude B (evenizedCoefficients (normalizeCoefficients qcs))) ^ 2)

def hullLength (R : Nat) (s : Rat) : Rat :=
  4 * R + |s|

theorem cell_certificate (R : Nat) (hR : 0 < R) (s : Rat) (d i m : Nat)
    (a b : Rat) (hcell : cellAt R s d i = some (a, b))
    (pcs qcs : List Rat) :
    checkCanonicalCell R (normalizeCoefficients pcs) (normalizeCoefficients qcs)
      s d i m (4 * m + 4) (genericCanonicalCellPayload R a b s m pcs qcs) = true ∧
    (genericCanonicalCellPayload R a b s m pcs qcs).norm.total.2 -
      (genericCanonicalCellPayload R a b s m pcs qcs).norm.total.1 ≤
      linearBudget R s pcs qcs * (b - a) +
        scalarBudget R s pcs qcs * (1 / 2 : Rat) ^ m := by
  have cellAt_strict (R : Nat) (s : Rat) (d i : Nat) (a b : Rat)
      (hcell : cellAt R s d i = some (a, b)) : a < b := by
    have hi : i < (canonicalPoints R s d).length := by
      by_contra hn
      have hnone := List.getElem?_eq_none (l := canonicalPoints R s d) (Nat.le_of_not_gt hn)
      simp [cellAt, hnone] at hcell
    have hj : i + 1 < (canonicalPoints R s d).length := by
      by_contra hn
      have hnone := List.getElem?_eq_none (l := canonicalPoints R s d) (Nat.le_of_not_gt hn)
      rw [cellAt, List.getElem?_eq_getElem hi, hnone] at hcell
      simp at hcell
    rw [cellAt, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at hcell
    change some ((canonicalPoints R s d)[i], (canonicalPoints R s d)[i + 1]) =
      some (a, b) at hcell
    injection hcell with hpair
    injection hpair with ha hb
    subst a
    subst b
    exact (Finset.sortedLT_sort (canonicalPointSet R s d)).getElem_lt_getElem_of_lt (by omega)
  have cellAt_mem_canonicalPoints (R : Nat) (s : Rat) (d i : Nat) (a b : Rat)
      (hcell : cellAt R s d i = some (a, b)) :
      a ∈ canonicalPoints R s d ∧ b ∈ canonicalPoints R s d := by
    have hi : i < (canonicalPoints R s d).length := by
      by_contra hn
      have hnone := List.getElem?_eq_none (l := canonicalPoints R s d) (Nat.le_of_not_gt hn)
      simp [cellAt, hnone] at hcell
    have hj : i + 1 < (canonicalPoints R s d).length := by
      by_contra hn
      have hnone := List.getElem?_eq_none (l := canonicalPoints R s d) (Nat.le_of_not_gt hn)
      rw [cellAt, List.getElem?_eq_getElem hi, hnone] at hcell
      simp at hcell
    have hidx := (show cellAt R s d i = some ((canonicalPoints R s d)[i],
          (canonicalPoints R s d)[i + 1]) from by
          simp [cellAt, List.getElem?_eq_getElem, hj,
            show i < (canonicalPoints R s d).length by omega])
    rw [hcell] at hidx
    injection hidx with hpair
    injection hpair with ha hb
    subst a
    subst b
    exact ⟨List.getElem_mem _, List.getElem_mem _⟩
  have hab := (cellAt_strict R s d i a b hcell).le
  have parser (u v : Rat) (cs : List Rat) (hcs : cs ≠ []) :
      coefficientsOfExpr (hornerInterval u v cs) = some cs := by
    have zeroPrefix (xs ys : List Rat) (hlen : xs.length ≤ ys.length) :
        coefficientAdd (xs.map (fun _ => (0 : Rat))) ys = ys := by
      induction xs generalizing ys with
      | nil => simp [coefficientAdd]
      | cons x xs ih =>
        cases ys with
        | nil => simp at hlen
        | cons y ys =>
          simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
          simp only [List.map_cons, coefficientAdd, zero_add, ih ys hlen]
    induction cs with
    | nil => contradiction
    | cons c cs ih =>
        cases cs with
        | nil => simp [hornerInterval, exactConstant, coefficientsOfExpr]
        | cons e es =>
          have ht := ih (by simp)
          have hmul : coefficientMul [0, 1] (e :: es) = 0 :: e :: es := by
            simp only [coefficientMul, List.cons_ne_self, List.map_cons,
              List.map_nil, zero_mul, one_mul]
            simp only [coefficientAdd, zero_add]
            have hz := zeroPrefix es (e :: es) (by simp)
            simpa only [List.map_map, Function.comp_def, zero_mul, if_false,
              if_true, List.map_id_fun', id_eq] using
              congrArg (List.cons (0 : Rat)) hz
          simp only [hornerInterval, intervalAdd, intervalMul, exactConstant,
            exactInput, coefficientsOfExpr, ht]
          simp [hmul, coefficientAdd]
  have provenance (u v : Rat) (cs : List Rat) :
      coefficientsOfExpr (hornerInterval u v
        (evenizedCoefficients (normalizeCoefficients cs))) =
        some (evenizedCoefficients (normalizeCoefficients cs)) := by
    apply parser
    unfold normalizeCoefficients
    split_ifs with h
    · simp [evenizedCoefficients, coefficientAdd, coefficientNegArgument]
    · cases cs with
      | nil => contradiction
      | cons c cs => simp [evenizedCoefficients, coefficientAdd, coefficientNegArgument]
  have minAbs (u v : Rat) (huv : u ≤ v) : absLower u v = shiftedMinAbs u v 0 := by
    unfold absLower shiftedMinAbs
    simp only [add_zero]
    by_cases hu : 0 ≤ u
    · have hv : 0 ≤ v := hu.trans huv
      rw [if_pos hu, abs_of_nonneg hu, abs_of_nonneg hv, min_eq_left huv]
      by_cases hu0 : u = 0
      · subst u; simp
      · rw [if_neg (by intro h; exact hu0 (le_antisymm h.1 hu))]
    · have hu' : u ≤ 0 := le_of_not_ge hu
      rw [if_neg hu]
      by_cases hv : v ≤ 0
      · rw [if_pos hv, abs_of_nonpos hu', abs_of_nonpos hv]
        by_cases hv0 : v = 0
        · subst v; simp [hu']
        · rw [if_neg (by intro h; exact hv0 (le_antisymm hv h.2)),
            min_eq_right (by linarith)]
      · have hv' : 0 ≤ v := le_of_not_ge hv
        simp [hv, hu', hv']
  have cutoff (u v : Rat) (huv : u ≤ v) :
      0 ≤ (cutoffCellBox R u v m (4 * m + 4)).1 ∧
      (cutoffCellBox R u v m (4 * m + 4)).1 ≤
        (cutoffCellBox R u v m (4 * m + 4)).2 ∧
      (cutoffCellBox R u v m (4 * m + 4)).2 ≤ 1 ∧
      (cutoffCellBox R u v m (4 * m + 4)).2 -
        (cutoffCellBox R u v m (4 * m + 4)).1 ≤
        9 * ((v - u) / R) + 2 * (1 / 2 : Rat) ^ m := by
    have hc := shiftedCutoffInterval_certificate (R : Rat) u v 0 m
      (by exact_mod_cast hR) huv
    simpa [cutoffCellBox, shiftedCutoffInterval, cutoffInterval,
      cutoffArgLower, cutoffArgUpper, shiftedCutoffArgLower,
      shiftedCutoffArgUpper, absUpper, shiftedMaxAbs, minAbs u v huv]
      using (show 0 ≤ (shiftedCutoffInterval (R : Rat) u v 0 m).1 ∧
        (shiftedCutoffInterval (R : Rat) u v 0 m).1 ≤
          (shiftedCutoffInterval (R : Rat) u v 0 m).2 ∧
        (shiftedCutoffInterval (R : Rat) u v 0 m).2 ≤ 1 ∧
        (shiftedCutoffInterval (R : Rat) u v 0 m).2 -
          (shiftedCutoffInterval (R : Rat) u v 0 m).1 ≤
          9 * ((v - u) / R) + 2 * (1 / 2 : Rat) ^ m from
          ⟨hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1,
            hc.2.2.2.2.2.2.2.2⟩)
  let payload := genericCanonicalCellPayload R a b s m pcs qcs
  have hh := cutoff a b hab
  have hs :
      0 ≤ (cutoffCellBox R (a - s) (b - s) m (4 * m + 4)).1 ∧
      (cutoffCellBox R (a - s) (b - s) m (4 * m + 4)).1 ≤
        (cutoffCellBox R (a - s) (b - s) m (4 * m + 4)).2 ∧
      (cutoffCellBox R (a - s) (b - s) m (4 * m + 4)).2 ≤ 1 ∧
      (cutoffCellBox R (a - s) (b - s) m (4 * m + 4)).2 -
        (cutoffCellBox R (a - s) (b - s) m (4 * m + 4)).1 ≤
        9 * ((b - a) / R) + 2 * (1 / 2 : Rat) ^ m := by
    have hc := shiftedCutoffInterval_certificate (R : Rat) a b (-s) m
      (by exact_mod_cast hR) hab
    have hid : cutoffCellBox R (a - s) (b - s) m (4 * m + 4) =
        shiftedCutoffInterval (R : Rat) a b (-s) m := by
      unfold cutoffCellBox cutoffArgLower cutoffArgUpper
      rw [minAbs (a - s) (b - s) (by linarith)]
      simp [shiftedCutoffInterval, cutoffInterval,
        cutoffArgLower, cutoffArgUpper, shiftedCutoffArgLower,
        shiftedCutoffArgUpper, absUpper, shiftedMaxAbs,
        shiftedMinAbs, sub_eq_add_neg]
    rw [hid]
    exact ⟨hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1,
      hc.2.2.2.2.2.2.2.2⟩
  have hp := horner_check a b hab (evenizedCoefficients (normalizeCoefficients pcs))
  have hq := horner_check a b hab (evenizedCoefficients (normalizeCoefficients qcs))
  have hps := horner_check (a - s) (b - s) (by linarith)
    (evenizedCoefficients (normalizeCoefficients pcs))
  have hqs := horner_check (a - s) (b - s) (by linarith)
    (evenizedCoefficients (normalizeCoefficients qcs))
  have ord (u v : Rat) (e : Expr 1) (huv : u ≤ v)
      (he : check (singleBox u v) e = true) : (bounds e).1 ≤ (bounds e).2 := by
    have hr := checked_expression_encloses (singleBox u v) (fun _ => (u : Real))
      (by intro j; exact ⟨le_rfl, by exact_mod_cast huv⟩) e he
    exact_mod_cast hr.1.trans hr.2
  have hph := ord a b payload.pHere hab hp
  have hqh := ord a b payload.qHere hab hq
  have hpsh := ord (a - s) (b - s) payload.pShift (by linarith) hps
  have hqsh := ord (a - s) (b - s) payload.qShift (by linarith) hqs
  have hnorm : check (cellInputBox R a b s m (4 * m + 4) payload)
      (cellNormSqExpr R a b s m (4 * m + 4) payload) = true := by
    let box := cellInputBox R a b s m (4 * m + 4) payload
    have hb : ∀ j, (box j).1 ≤ (box j).2 := by
      intro j
      fin_cases j
      · exact hh.2.1
      · exact hs.2.1
      · exact hph
      · exact hqh
      · exact hpsh
      · exact hqsh
    let x (j : Fin 6) : Expr 6 := .input j (box j).1 (box j).2
    have hx (j : Fin 6) : check box (x j) = true := by simp [x, check, hb j]
    let pe (j k : Fin 6) : Expr 6 :=
      .mul (productBounds (box j) (box k)).1 (productBounds (box j) (box k)).2
        (x j) (x k)
    have hc (j k : Fin 6) : check box (pe j k) = true := by
      simp [pe, check, hx, x, bounds, productBounds, productLower, productUpper, hb]
    have ordered (e : Expr 6) (he : check box e = true) :
        (bounds e).1 ≤ (bounds e).2 := by
      have hv := checked_expression_encloses box (fun j => ((box j).1 : Real))
        (by intro j; exact ⟨le_rfl, by exact_mod_cast hb j⟩) e he
      exact_mod_cast hv.1.trans hv.2
    have dc (e f : Expr 6) (he : check box e = true) (hf : check box f = true) :
        check box (differenceExpr e f) = true := by
      have hn : check box (.neg (-(bounds f).2) (-(bounds f).1) f) = true := by
        simp [check, hf, neg_le_neg (ordered f hf)]
      change (check box e && (check box (.neg _ _ f) && decide _)) = true
      rw [he, hn, Bool.true_and, Bool.true_and]
      apply decide_eq_true
      change (bounds e).1 - (bounds f).2 ≤ (bounds e).2 - (bounds f).1 ∧
        (bounds e).1 - (bounds f).2 ≤ (bounds e).1 + -(bounds f).2 ∧
        (bounds e).2 + -(bounds f).1 ≤ (bounds e).2 - (bounds f).1
      exact ⟨sub_le_sub (ordered e he) (ordered f hf), by simp [sub_eq_add_neg],
        by simp [sub_eq_add_neg]⟩
    have hr := square_factory_correct box (differenceExpr (pe 0 2) (pe 1 4))
      (dc _ _ (hc 0 2) (hc 1 4))
    have hi := square_factory_correct box (differenceExpr (pe 0 3) (pe 1 5))
      (dc _ _ (hc 0 3) (hc 1 5))
    change check box (normSqExpr (differenceExpr (pe 0 2) (pe 1 4))
      (differenceExpr (pe 0 3) (pe 1 5))) = true
    change (check box (squareExpr _) && (check box (squareExpr _) && decide _)) = true
    rw [hr.2.2.1, hi.2.2.1, Bool.true_and, Bool.true_and]
    apply decide_eq_true
    exact ⟨add_le_add hr.2.1 hi.2.1, le_rfl, le_rfl⟩
  have haccept : checkCanonicalCell R (normalizeCoefficients pcs)
      (normalizeCoefficients qcs) s d i m (4 * m + 4) payload = true := by
    apply decide_eq_true
    simp only [canonicalCellAccepted, hcell]
    exact ⟨hR, hab, (checkCutoffLogistic_all_precision _ m).1,
      (checkCutoffLogistic_all_precision _ m).1,
      (checkCutoffLogistic_all_precision _ m).1,
      (checkCutoffLogistic_all_precision _ m).1,
      provenance a b pcs, provenance a b qcs,
      provenance (a - s) (b - s) pcs, provenance (a - s) (b - s) qcs,
      hp, hq, hps, hqs, hnorm⟩
  refine ⟨haccept, ?_⟩
  let B := coordinateBudget R s
  let p := evenizedCoefficients (normalizeCoefficients pcs)
  let q := evenizedCoefficients (normalizeCoefficients qcs)
  let Ap := amplitude B p
  let Aq := amplitude B q
  have hB : 0 ≤ B := by dsimp [B, coordinateBudget]; positivity
  have hAp : 0 ≤ Ap := amplitude_nonneg B hB p
  have hAq : 0 ≤ Aq := amplitude_nonneg B hB q
  have coord (u : Rat) (hu : u ∈ canonicalPoints R s d) :
      -B ≤ u ∧ u ≤ B ∧ -B ≤ u - s ∧ u - s ≤ B := by
    have hc := canonicalPoint_mem_hull R s u d hu
    have hlo : -B ≤ supportHullLower R s := by
      dsimp [B, coordinateBudget, supportHullLower]
      apply le_min <;> linarith [neg_abs_le s, abs_nonneg s]
    have hhi : supportHullUpper R s ≤ B := by
      dsimp [B, coordinateBudget, supportHullUpper]
      apply max_le <;> linarith [le_abs_self s, abs_nonneg s]
    have hlos : -B + s ≤ supportHullLower R s := by
      dsimp [B, coordinateBudget, supportHullLower]
      apply le_min <;> linarith [le_abs_self s, abs_nonneg s]
    have hhis : supportHullUpper R s ≤ B + s := by
      dsimp [B, coordinateBudget, supportHullUpper]
      apply max_le <;> linarith [neg_abs_le s, abs_nonneg s]
    exact ⟨hlo.trans hc.1, hc.2.trans hhi, by linarith [hc.1], by linarith [hc.2]⟩
  have hmem := cellAt_mem_canonicalPoints R s d i a b hcell
  have ha := coord a hmem.1
  have hb := coord b hmem.2
  have ph := horner_interval_bounds a b B hab hB ha.1 hb.2.1 p
  have qh := horner_interval_bounds a b B hab hB ha.1 hb.2.1 q
  have ps := horner_interval_bounds (a - s) (b - s) B (by linarith)
    hB ha.2.2.1 hb.2.2.2 p
  have qs := horner_interval_bounds (a - s) (b - s) B (by linarith)
    hB ha.2.2.1 hb.2.2.2 q
  have prod (w : Rat × Rat) (e : Expr 1) (A D ell : Rat)
      (hA : 0 ≤ A) (hw : 0 ≤ w.1 ∧ w.1 ≤ w.2 ∧ w.2 ≤ 1 ∧
        w.2 - w.1 ≤ 9 * (ell / R) + 2 * (1 / 2 : Rat) ^ m)
      (he : -A ≤ (bounds e).1 ∧ (bounds e).1 ≤ (bounds e).2 ∧
        (bounds e).2 ≤ A ∧ (bounds e).2 - (bounds e).1 ≤ D * ell) :
      -A ≤ (productBounds w (bounds e)).1 ∧
      (productBounds w (bounds e)).1 ≤ (productBounds w (bounds e)).2 ∧
      (productBounds w (bounds e)).2 ≤ A ∧
      (productBounds w (bounds e)).2 - (productBounds w (bounds e)).1 ≤
        A * (9 * (ell / R) + 2 * (1 / 2 : Rat) ^ m) + D * ell := by
    have hwl : |w.1| ≤ 1 := by rw [abs_of_nonneg hw.1]; linarith [hw.2.1, hw.2.2.1]
    have hwu : |w.2| ≤ 1 := by rw [abs_of_nonneg (hw.1.trans hw.2.1)]; exact hw.2.2.1
    have hel : |(bounds e).1| ≤ A := abs_le.mpr ⟨he.1, he.2.1.trans he.2.2.1⟩
    have heu : |(bounds e).2| ≤ A := abs_le.mpr ⟨he.1.trans he.2.1, he.2.2.1⟩
    have hwidth := product_width w.1 w.2 (bounds e).1 (bounds e).2 A 1
      hw.2.1 he.2.1 hwl hwu hel heu hA (by norm_num)
    refine ⟨by simpa [productBounds] using hwidth.1, ?_,
      by simpa [productBounds] using hwidth.2.1, ?_⟩
    · simp [productBounds, productLower, productUpper]
    · dsimp only [productBounds]
      nlinarith [hwidth.2.2, mul_le_mul_of_nonneg_left hw.2.2.2 hA]
  have prh := prod _ _ Ap (slope B p) (b - a) hAp hh ph
  have prs := prod _ _ Ap (slope B p) (b - a) hAp
    (by simpa only [sub_sub_sub_cancel_right] using hs)
    (by simpa only [sub_sub_sub_cancel_right] using ps)
  have pqh := prod _ _ Aq (slope B q) (b - a) hAq hh qh
  have pqs := prod _ _ Aq (slope B q) (b - a) hAq
    (by simpa only [sub_sub_sub_cancel_right] using hs)
    (by simpa only [sub_sub_sub_cancel_right] using qs)
  have hn := norm_sq_difference_width_le Ap Aq
    _ _ _ _ _ _ _ _ hAp hAq prh.2.1 prs.2.1 pqh.2.1 pqs.2.1
    prh.1 prh.2.2.1 prs.1 prs.2.2.1 pqh.1 pqh.2.2.1 pqs.1 pqs.2.2.1
  have hpw := mul_le_mul_of_nonneg_left (add_le_add prh.2.2.2 prs.2.2.2)
    (show 0 ≤ 4 * Ap by positivity)
  have hqw := mul_le_mul_of_nonneg_left (add_le_add pqh.2.2.2 pqs.2.2.2)
    (show 0 ≤ 4 * Aq by positivity)
  change (normSqBounds (differenceBounds _ _) (differenceBounds _ _)).2 -
    (normSqBounds (differenceBounds _ _) (differenceBounds _ _)).1 ≤ _
  calc
    _ ≤ _ := hn.2.2.2
    _ ≤ 4 * Ap * (2 * (Ap * (9 * ((b - a) / R) + 2 * (1 / 2 : Rat) ^ m) +
        slope B p * (b - a))) +
      4 * Aq * (2 * (Aq * (9 * ((b - a) / R) + 2 * (1 / 2 : Rat) ^ m) +
        slope B q * (b - a))) := by linear_combination hpw + hqw
    _ = _ := by dsimp [linearBudget, scalarBudget, Ap, Aq, B, p, q]; ring

#print axioms cell_certificate
end D5.S3.Weil.Separator.TranslationEnergy.Generic
