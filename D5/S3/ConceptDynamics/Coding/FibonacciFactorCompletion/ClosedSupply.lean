/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ClosedSupply
   generality: G
   anchors: []
   utility: none
   digest: Owned endpoint equality controls closed supplies and finite actual resets. -/

import D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
import D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Constructions
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.EReal.Basic
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

/-- Closed active costs on actual return inputs, including nearest-point ownership. -/
def ClosedControl (j : Side) (o : Ownership) (b : ℝ) : List Return → ℝ → Prop
  | [], _ => True
  | a :: rest, D =>
      (lam - g ^ 2 * (chi ^ a.r * D) < b ∨
        (lam - g ^ 2 * (chi ^ a.r * D) = b ∧
          (match j with | .high => o 0 = true | .low => o 1 = false))) ∧
      ClosedControl j o b rest (returnMap j a D)

set_option maxHeartbeats 1600000 in
-- All repetitions and owned-endpoint errors are assembled on the same sources.
/-- Closed errors are constructed on the same paired literal sources; only the
high owned nearest point can attain a high-return budget equality. -/
theorem actual_closed_record_supply (model : Model) (o : Ownership) (b : ℝ)
    (execution : List Return) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K))) :
    ActualPairSupply model o b .closed execution ↔
      GuardTrace K ((lam - b) / g ^ 2 / chi ^ K) (!o 0) .high execution
        (initial .high model) := by
  classical
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have root : g ^ 2 + 4 * g = 1 := by dsimp [g, t]; nlinarith
  have gp : 0 < g := by dsimp [g, t]; nlinarith
  have gq : g < 1 / 4 := by nlinarith
  have rp : 0 < rho := pow_pos gp 6
  have cp : 0 < chi := pow_pos gp 20
  have r1 : rho < 1 := by
    exact pow_lt_one₀ gp.le (by linarith) (by decide)
  have c1 : chi < 1 := by
    exact pow_lt_one₀ gp.le (by linarith) (by decide)
  have tg : t = (1 + g) / 2 := by dsimp [g]; ring
  have hp (j : Side) : 0 < hSide j ∧ hSide j < eSide j := by
    cases j <;> dsimp [hSide, eSide, c0, T2] <;>
      rw [tg] <;> constructor <;> linarith
  have g2p : 0 < g ^ 2 := pow_pos gp 2
  have cKp : 0 < chi ^ K := pow_pos cp K
  have cKle : chi ^ K ≤ chi := by
    simpa only [pow_one] using
      pow_le_pow_of_le_one cp.le c1.le (show 1 ≤ K by omega)
  have chi4 : chi ≤ g ^ 4 :=
    pow_le_pow_of_le_one gp.le (by linarith) (by decide)
  have h1 : hSide .high < 1 := by dsimp [hSide]; linarith
  have cKh : chi ^ K * hSide .high < chi :=
    lt_of_lt_of_le (by simpa using mul_lt_mul_of_pos_left h1 cKp) cKle
  have powerId : g ^ 2 * g ^ 4 = rho := by dsimp [rho]; ring
  have costSmall : g ^ 2 * chi ^ K * hSide .high < rho := by
    have x := mul_lt_mul_of_pos_left cKh g2p
    have y := mul_le_mul_of_nonneg_left chi4 g2p.le
    rw [powerId] at y
    nlinarith
  have hb : lam - rho < b := by linarith
  have ap (j : Side) : 0 < aSide j := mul_pos (sub_pos.mpr r1) (hp j).1
  have bp : 0 < b := by
    have hr : rho < 1 / 4096 := by
      have h := pow_lt_pow_left₀ gq gp.le (by decide : (6 : ℕ) ≠ 0)
      norm_num [rho] at h ⊢; exact h
    have ht : t = (1 + g) / 2 := by dsimp [g]; ring
    have hl : 3 / 80 < lam := by dsimp [lam, T2]; rw [ht]; linarith
    linarith
  let condition (j : Side) (D : ℝ) : Prop :=
    lam - g ^ 2 * D < b ∨ (lam - g ^ 2 * D = b ∧
      (match j with | .high => o 0 = true | .low => o 1 = false))
  have monoCondition (j : Side) (D E : ℝ) (hDE : D ≤ E)
      (hc : condition j D) : condition j E := by
    by_cases heq : D = E
    · simpa only [heq] using hc
    · have gain := mul_pos g2p (sub_pos.mpr (lt_of_le_of_ne hDE heq))
      have bound : lam - g ^ 2 * D ≤ b := by
        rcases hc with h | ⟨h, _⟩ <;> linarith
      exact Or.inl (by nlinarith)
  have app := literal_source_geometry.2.2.2.2
  have appendSupply (w v : List Label) (cs ds : List Color) (z : ℝ)
      (len : w.length = cs.length) :
      BlockSupply o b false (w ++ v) (cs ++ ds) z ↔
        BlockSupply o b false w cs (compose v z) ∧ BlockSupply o b false v ds z := by
    constructor
    · intro h; constructor
      · intro p hpc
        have hpp : p < (cs ++ ds).length := by simp only [List.length_append]; omega
        obtain ⟨e, he, ho⟩ := h p hpp
        refine ⟨e, he, ?_⟩
        have hd : (w ++ v).drop p = w.drop p ++ v := by
          exact List.drop_append_of_le_length (by omega)
        simpa only [hd, app, List.getElem_append_left hpc] using ho
      · intro p hpd
        have hpp : cs.length + p < (cs ++ ds).length := by simp only [List.length_append]; omega
        obtain ⟨e, he, ho⟩ := h (cs.length + p) hpp
        refine ⟨e, he, ?_⟩
        have hd : (w ++ v).drop (cs.length + p) = v.drop p := by
          rw [List.drop_append, ← len, List.drop_eq_nil_of_le (by omega)]
          simp
        simpa only [hd, List.getElem_append_right (as := cs) (bs := ds) (i := cs.length + p) (by omega), Nat.add_sub_cancel_left] using ho
    · rintro ⟨hw, hv⟩ p hpc
      by_cases hleft : p < cs.length
      · obtain ⟨e, he, ho⟩ := hw p hleft
        refine ⟨e, he, ?_⟩
        have hd : (w ++ v).drop p = w.drop p ++ v :=
          List.drop_append_of_le_length (by omega)
        simpa only [hd, app, List.getElem_append_left hleft] using ho
      · have hright : p - cs.length < ds.length := by simp only [List.length_append] at hpc; omega
        obtain ⟨e, he, ho⟩ := hv (p - cs.length) hright
        refine ⟨e, he, ?_⟩
        have hd : (w ++ v).drop p = v.drop (p - cs.length) := by
          rw [List.drop_append, len, List.drop_eq_nil_of_le (by omega)]; simp
        simpa only [hd, List.getElem_append_right (as := cs) (bs := ds) (i := p) (by omega)] using ho
  have repeatLength (w : List Label) (n : ℕ) : (repeatWord w n).length = w.length * n := by
    induction n with
    | zero => simp [repeatWord]
    | succ n ih => simp [repeatWord, ih, Nat.mul_add]; omega
  have repeatAct (j : Side) (n : ℕ) (D : ℝ) :
      compose (repeatWord (block j) n) (c0 + sign j * D) =
        c0 + sign j * (hSide j - rho ^ n * (hSide j - D)) := by
    induction n with
    | zero => simp [repeatWord, compose]
    | succ n ih =>
      rw [repeatWord, app, ih,
        (paired_source_reconstruction j .original []).2.2.2.2.2.2.2.1]
      dsimp [aSide]; rw [pow_succ]; ring
  have repeatCAct (j : Side) (n : ℕ) (D : ℝ) :
      compose (repeatWord C n) (c0 + sign j * D) = c0 + sign j * (chi ^ n * D) := by
    induction n with
    | zero => simp [repeatWord, compose]
    | succ n ih =>
      rw [repeatWord, app, ih,
        (paired_source_reconstruction j .original []).2.2.2.2.2.2.1]
      rw [pow_succ]; ring
  have domain (j : Side) (D : ℝ) (hD : 0 < D ∧ D < hSide j) :
      0 ≤ c0 + sign j * D ∧ c0 + sign j * D ≤ T2 := by
    have hE := lt_trans hD.2 (hp j).2
    cases j <;> dsimp [sign, eSide, c0, T2] at * <;> constructor <;> linarith
  have csLength : ∀ n : ℕ, ((List.replicate n colorsD).flatten).length = 6 * n := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih, colorsD]; omega
  have six (j : Side) (n : ℕ) (D : ℝ) (hD : 0 < D ∧ D < hSide j) :
      BlockSupply o b false (repeatWord (block j) n)
        (List.replicate n colorsD).flatten (c0 + sign j * D) ↔
      (0 < n → condition j D) := by
    induction n with
    | zero => simp [repeatWord, BlockSupply]
    | succ n ih =>
      have len : (block j).length = colorsD.length := by cases j <;> rfl
      rw [repeatWord, List.replicate_succ, List.flatten_cons,
        appendSupply _ _ _ _ _ len, repeatAct]
      have dn : 0 < hSide j - rho ^ n * (hSide j - D) ∧
          hSide j - rho ^ n * (hSide j - D) < hSide j := by
        have rr := pow_pos rp n
        have rl : rho ^ n ≤ 1 := pow_le_one₀ rp.le r1.le
        have gg := mul_pos rr (sub_pos.mpr hD.2)
        have gl := mul_le_mul_of_nonneg_right rl (sub_pos.mpr hD.2).le
        constructor <;> nlinarith [hD.1]
      change (BlockSupply o b false (block j) colorsD
        (c0 + sign j * (hSide j - rho ^ n * (hSide j - D))) ∧
        BlockSupply o b false (repeatWord (block j) n)
          (List.replicate n colorsD).flatten (c0 + sign j * D)) ↔ _
      rw [(literal_full_slot_readout o b hb).2.1 j _ dn.1 (le_of_lt (lt_trans dn.2 (hp j).2)), ih]
      have lower : D ≤ hSide j - rho ^ n * (hSide j - D) := by
        have rl : rho ^ n ≤ 1 := pow_le_one₀ rp.le r1.le
        have gl := mul_le_mul_of_nonneg_right rl (sub_pos.mpr hD.2).le
        linarith
      have gg : 0 < g ^ 2 := pow_pos gp 2
      constructor
      · rintro ⟨houter, hinner⟩ _
        cases n with
        | zero => cases j <;> simpa [condition] using houter
        | succ n => exact hinner (by omega)
      · intro h
        constructor
        · exact monoCondition j D _ lower (h (by omega))
        · intro _; exact h (by omega)
  have twenty (j : Side) (n : ℕ) (D : ℝ) (hD : 0 < D ∧ D < hSide j) :
      BlockSupply o b false (repeatWord C n)
        (List.replicate n colorsE).flatten (c0 + sign j * D) := by
    induction n with
    | zero => simp [BlockSupply]
    | succ n ih =>
      rw [repeatWord, List.replicate_succ, List.flatten_cons,
        appendSupply _ _ _ _ _ (by rfl), repeatCAct]
      refine ⟨?_, ih⟩
      have pp := pow_pos cp n
      have pl : chi ^ n ≤ 1 := pow_le_one₀ cp.le c1.le
      have dn : 0 < chi ^ n * D ∧ chi ^ n * D < hSide j := by
        constructor
        · exact mul_pos pp hD.1
        · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right pl hD.1.le) (by simpa only [one_mul] using hD.2)
      intro p hp
      obtain ⟨e, he, ho⟩ := (literal_full_slot_readout o b hb).2.2 _
        (domain j _ dn).1 (domain j _ dn).2 p hp
      exact ⟨e, he.le, ho⟩
  have returns (j : Side) (a : Return) (D : ℝ) (hD : 0 < D ∧ D < hSide j) :
      BlockSupply o b false (returnWord j a) (returnColors a) (c0 + sign j * D) ↔
        condition j (chi ^ a.r * D) := by
    have len : (repeatWord (block j) a.m).length = (List.replicate a.m colorsD).flatten.length := by
      rw [repeatLength, csLength]; cases j <;> rfl
    rw [returnWord, returnColors, appendSupply _ _ _ _ _ len, repeatCAct]
    have pp := pow_pos cp a.r
    have pl : chi ^ a.r ≤ 1 := pow_le_one₀ cp.le c1.le
    have dn : 0 < chi ^ a.r * D ∧ chi ^ a.r * D < hSide j := by
      constructor
      · exact mul_pos pp hD.1
      · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right pl hD.1.le) (by simpa only [one_mul] using hD.2)
    rw [six j a.m _ dn]
    simp only [a.m_pos, forall_const, twenty j a.r D hD, and_true]
  have extLen (j : Side) (xs : List Return) : (externalWord j xs).length =
      (xs.reverse.map returnColors).flatten.length := by
    have a := (paired_source_reconstruction j .original xs).2.2.2.2.1
    have b := (paired_source_reconstruction j .original xs).2.2.2.2.2.1
    have st : (stem j).length = 26 := by cases j <;> rfl
    have hd : colorsD.length = 6 := rfl
    have he : colorsE.length = 20 := rfl
    simp only [observedPrefix, history, List.length_append, anchor, List.length_nil,
      Nat.add_zero, st, hd, he] at a b
    omega
  have boundary := actual_complete_boundary_geometry model execution
  have initialDomain (j : Side) (md : Model) : 0 < initial j md ∧ initial j md < hSide j := by
    have h := (actual_complete_boundary_geometry md []).1 j 0
    simp only [List.take_nil, execute] at h
    exact ⟨lt_trans (ap j) h.1, h.2⟩
  have runDomain (j : Side) (xs : List Return) (md : Model) :
      0 < execute j xs (initial j md) ∧ execute j xs (initial j md) < hSide j := by
    have h := (actual_complete_boundary_geometry md xs).1 j xs.length
    rw [List.take_length] at h
    exact ⟨lt_trans (ap j) h.1, h.2⟩
  have stemSupply (j : Side) (D : ℝ) (hD : 0 < D ∧ D < hSide j) :
      BlockSupply o b false (stem j) (colorsD ++ colorsE) (c0 + sign j * D) ↔
        condition j (chi * D) := by
    have h := returns j ⟨1, 1, by decide, by decide⟩ D hD
    simpa only [returnWord, returnColors, repeatWord, List.append_nil,
      List.replicate_succ, List.replicate_zero, List.flatten_cons, List.flatten_nil,
      stem, pow_one] using h
  have pairErrors : ActualPairSupply model o b .closed execution ↔
      ∀ j : Side, BlockSupply o b false (observedPrefix j model execution)
        (history model execution) (coordinate (tailPrefix j) 0) := by
    have lengthEq (j : Side) : (observedPrefix j model execution).length =
        (history model execution).length := by
      rw [(paired_source_reconstruction j model execution).2.2.2.2.1,
        (paired_source_reconstruction j model execution).2.2.2.2.2.1]
    have coord (j : Side) (p : ℕ) (hp : p < (history model execution).length) :
        coordinate (sourcePrefix j model execution) p =
        compose ((observedPrefix j model execution).drop p) (coordinate (tailPrefix j) 0) := by
      rw [coordinate, sourcePrefix, List.drop_append_of_le_length (by rw [lengthEq]; omega), app]
      rfl
    constructor
    · intro h j p hp
      obtain ⟨err, herr, hread, hzero, hfuture⟩ := h j
      refine ⟨err p, herr p, ?_⟩
      rw [← coord j p hp]; exact hread p hp
    · intro h j
      let choice (p : ℕ) (hp : p < (history model execution).length) : ℝ :=
        Classical.choose (h j p hp)
      let err (p : ℕ) : ℝ := if hp : p < (history model execution).length then choice p hp else 0
      refine ⟨err, ?_, ?_, ?_, ?_⟩
      · intro p; dsimp [err]; split_ifs with hp
        · exact (Classical.choose_spec (h j p hp)).1
        · simpa using bp.le
      · intro p hp
        dsimp [err]; rw [dif_pos hp, coord j p hp]
        exact (Classical.choose_spec (h j p hp)).2
      · intro p hp; dsimp [err]; rw [dif_neg (by omega)]
      · intro p
        have hz : err ((observedPrefix j model execution).length + p) = 0 := by
          dsimp [err]; rw [dif_neg (by rw [lengthEq]; omega)]
        rw [hz, (paired_source_reconstruction j model execution).2.2.1]
  have costs : ActualPairSupply model o b .closed execution ↔
      condition .high (chi * execute .high execution (initial .high model)) ∧
      (model = .anchored → condition .high (chi * xSide .high)) ∧
      ClosedControl .high o b execution (initial .high model) := by
    rw [pairErrors]

    have returnDomain (j : Side) (a : Return) (D : ℝ) (hD : 0 < D ∧ D < hSide j) :
        0 < returnMap j a D ∧ returnMap j a D < hSide j := by
      have rr := pow_pos rp a.m
      have rl : rho ^ a.m ≤ 1 := pow_le_one₀ rp.le r1.le
      have cc := pow_pos cp a.r
      have cl : chi ^ a.r ≤ 1 := pow_le_one₀ cp.le c1.le
      have cz : 0 < chi ^ a.r * D := mul_pos cc hD.1
      have ch : chi ^ a.r * D < hSide j :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right cl hD.1.le) (by simpa only [one_mul] using hD.2)
      have gap := mul_pos rr (sub_pos.mpr ch)
      have low := mul_le_mul_of_nonneg_right rl (sub_pos.mpr ch).le
      dsimp [returnMap]; constructor <;> nlinarith
    have extSupply (j : Side) (xs : List Return) (D : ℝ) (hD : 0 < D ∧ D < hSide j) :
        BlockSupply o b false (externalWord j xs) (xs.reverse.map returnColors).flatten
          (c0 + sign j * D) ↔ ClosedControl j o b xs D := by
      induction xs generalizing D with
      | nil => simp [externalWord, BlockSupply, ClosedControl]
      | cons a xs ih =>
        simp only [externalWord, List.reverse_cons, List.map_append, List.map_cons,
          List.map_nil, List.flatten_append, List.flatten_cons, List.flatten_nil,
          List.append_nil]
        change BlockSupply o b false (externalWord j xs ++ returnWord j a)
          ((xs.reverse.map returnColors).flatten ++ returnColors a) (c0 + sign j * D) ↔
          ClosedControl j o b (a :: xs) D
        rw [appendSupply _ _ _ _ _ (extLen j xs),
          (paired_source_reconstruction j .original []).2.2.2.2.2.2.2.2.1,
          ih _ (returnDomain j a D hD), returns j a D hD]
        change (ClosedControl j o b xs (returnMap j a D) ∧
          condition j (chi ^ a.r * D)) ↔
          (condition j (chi ^ a.r * D) ∧ ClosedControl j o b xs (returnMap j a D))
        exact and_comm
    have anchorTail (j : Side) : compose (anchor j model) (coordinate (tailPrefix j) 0) =
        c0 + sign j * initial j model := by
      have h := (paired_source_reconstruction j model []).2.2.2.1
      simpa only [externalWord, List.reverse_nil, List.map_nil, List.flatten_nil,
        List.nil_append, coordinate, List.drop_zero, app, execute] using h
    have anchorSupply (j : Side) (md : Model) :
        BlockSupply o b false (anchor j md)
          (match md with | .original => [] | .anchored => colorsD ++ colorsE)
          (coordinate (tailPrefix j) 0) ↔
        (md = .anchored → condition j (chi * xSide j)) := by
      have tail := (paired_source_reconstruction j .original []).2.2.2.2.2.2.2.2.2.2
      cases md with
      | original => simp [anchor, BlockSupply]
      | anchored =>
        simp only [anchor, coordinate, List.drop_zero, tail, true_implies]
        exact stemSupply j (xSide j) (initialDomain j .original)
    have wholeSide (j : Side) :
        BlockSupply o b false (observedPrefix j model execution) (history model execution)
          (coordinate (tailPrefix j) 0) ↔
        condition j (chi * execute j execution (initial j model)) ∧
        (model = .anchored → condition j (chi * xSide j)) ∧
        ClosedControl j o b execution (initial j model) := by
      have len : (stem j).length = (colorsD ++ colorsE).length := by cases j <;> rfl
      simp only [observedPrefix, history]
      rw [List.append_assoc (stem j), List.append_assoc (colorsD ++ colorsE)]
      rw [appendSupply _ _ _ _ _ len, appendSupply _ _ _ _ _ (extLen j execution),
        app, anchorTail,
        (paired_source_reconstruction j .original []).2.2.2.2.2.2.2.2.2.1,
        stemSupply j _ (runDomain j execution model), extSupply j execution _ (initialDomain j model)]
      exact ⟨fun h => ⟨h.1, (anchorSupply j model).mp h.2.2, h.2.1⟩,
        fun h => ⟨h.1, h.2.2, (anchorSupply j model).mpr h.2.1⟩⟩
    have hh : hSide .high < hSide .low := by dsimp [hSide]; linarith
    have returnOrder (a : Return) (DH DL : ℝ) (ho : DH < DL) :
        returnMap .high a DH < returnMap .low a DL := by
      have rr := pow_pos rp a.m
      have rl := pow_lt_one₀ rp.le r1 (Nat.ne_of_gt a.m_pos)
      have cc := pow_pos cp a.r
      have gainH := mul_pos (sub_pos.mpr rl) (sub_pos.mpr hh)
      have gainD := mul_pos (mul_pos rr cc) (sub_pos.mpr ho)
      dsimp [returnMap]; nlinarith
    have controlOrder (xs : List Return) (DH DL : ℝ) (ho : DH < DL)
        (hc : ClosedControl .high o b xs DH) : ClosedControl .low o b xs DL := by
      induction xs generalizing DH DL with
      | nil => trivial
      | cons a xs ih =>
        refine ⟨?_, ih _ _ (returnOrder a DH DL ho) hc.2⟩
        have gain := mul_pos (mul_pos (pow_pos gp 2) (pow_pos cp a.r)) (sub_pos.mpr ho)
        have h : lam - g ^ 2 * chi ^ a.r * DH ≤ b := by
          rcases hc.1 with h | ⟨h, _⟩ <;> linarith
        exact Or.inl (by nlinarith)
    have io : initial .high model < initial .low model := by
      simpa only [List.take_zero, execute] using boundary.2.1 0
    have xo : xSide .high < xSide .low := by
      simpa only [List.take_nil, execute, initial] using
        (actual_complete_boundary_geometry .original []).2.1 0
    have eo : execute .high execution (initial .high model) <
        execute .low execution (initial .low model) := by
      simpa only [List.take_length] using boundary.2.1 execution.length
    constructor
    · intro h; exact (wholeSide .high).mp (h .high)
    · rintro ⟨hstem, hanchor, hcontrol⟩ j
      apply (wholeSide j).mpr
      cases j with
      | high => exact ⟨hstem, hanchor, hcontrol⟩
      | low =>
        have coeff := mul_pos (pow_pos gp 2) cp
        have gstem := mul_pos coeff (sub_pos.mpr eo)
        have ganchor := mul_pos coeff (sub_pos.mpr xo)
        refine ⟨?_, ?_, controlOrder execution _ _ io hcontrol⟩
        · have h : lam - g ^ 2 * (chi * execute .high execution (initial .high model)) ≤ b := by
            rcases hstem with h | ⟨h, _⟩ <;> linarith
          exact Or.inl (by nlinarith)
        · intro hm
          have h : lam - g ^ 2 * (chi * xSide .high) ≤ b := by
            rcases hanchor hm with h | ⟨h, _⟩ <;> linarith
          exact Or.inl (by nlinarith)
  -- The scalar cap is derived after the fixed-source error assembly.
  let H : ℝ := hSide .high
  let A : ℝ := aSide .high
  let Z : ℝ := A / (1 - rho * chi ^ K)
  let S : ℝ := (lam - b) / g ^ 2
  let d : ℝ := S / chi ^ K
  have Hp : 0 < H := (hp .high).1
  have Ap : 0 < A := ap .high
  have rbound : rho < 1 / 4096 := by
    have h := pow_lt_pow_left₀ gq gp.le (by decide : (6 : ℕ) ≠ 0)
    norm_num [rho] at h ⊢; exact h
  have cbound : chi < 1 / 256 := by
    have h := pow_lt_pow_left₀ gq gp.le (by decide : (4 : ℕ) ≠ 0)
    norm_num at h
    exact lt_of_le_of_lt chi4 h
  have gap : chi * H < A := by
    have x := mul_lt_mul_of_pos_right (show chi < 1 - rho by linarith) Hp
    exact x
  have den : 0 < 1 - rho * chi ^ K := by
    have x : chi ^ K ≤ 1 := pow_le_one₀ cp.le c1.le
    have y := mul_le_mul_of_nonneg_left x rp.le
    nlinarith
  have AZ : A < Z := by
    apply (lt_div_iff₀ den).mpr
    have x := mul_pos Ap (mul_pos rp cKp)
    nlinarith
  have ZS : chi ^ K * Z < S := by
    apply (lt_div_iff₀ g2p).mpr
    dsimp [Z, A] at *
    nlinarith only [hbp]
  have Sd : S = chi ^ K * d := by
    dsimp [d]; field_simp
  have SH : S < chi ^ K * H := by
    apply (div_lt_iff₀ g2p).mpr
    nlinarith only [hqb]
  have cK2 : chi ^ K ≤ chi ^ 2 :=
    pow_le_pow_of_le_one cp.le c1.le hK
  have auto (D : ℝ) (hD : A < D) : lam - g ^ 2 * chi * D < b := by
    have x := mul_lt_mul_of_pos_left hD cp
    have y := mul_lt_mul_of_pos_left gap cp
    have z := mul_le_mul_of_nonneg_right cK2 Hp.le
    have small : S < chi * D := by nlinarith
    have w := (div_lt_iff₀ g2p).mp small
    nlinarith
  have returnInterval (a : Return) (D : ℝ) (hD : A < D ∧ D < H) :
      A < returnMap .high a D ∧ returnMap .high a D < H := by
    have Dp : 0 < D := lt_trans Ap hD.1
    have rr := pow_pos rp a.m
    have cc := pow_pos cp a.r
    have cl : chi ^ a.r ≤ 1 := pow_le_one₀ cp.le c1.le
    have rl : rho ^ a.m ≤ rho := by
      simpa only [pow_one] using pow_le_pow_of_le_one rp.le r1.le a.m_pos
    have ch : chi ^ a.r * D < H := by nlinarith
    have upper := mul_pos rr (sub_pos.mpr ch)
    have lower := mul_le_mul_of_nonneg_right rl (sub_pos.mpr ch).le
    have gain := mul_pos rp (mul_pos cc Dp)
    dsimp [returnMap, A, H, aSide] at *
    constructor <;> nlinarith
  have scalar (a : Return) (D : ℝ) (hD : A < D ∧ D < H) :
      condition .high (chi ^ a.r * D) ↔
      a.r ≤ K ∧ (a.r = K → if !o 0 then d < D else d ≤ D) := by
    have Dp : 0 < D := lt_trans Ap hD.1
    have criterion : condition .high (chi ^ a.r * D) ↔
        S < chi ^ a.r * D ∨ (S = chi ^ a.r * D ∧ o 0 = true) := by
      dsimp [condition]
      have sd : S * g ^ 2 = lam - b := by dsimp [S]; field_simp
      constructor
      · rintro (h | ⟨h, ho⟩)
        · exact Or.inl (by nlinarith)
        · exact Or.inr ⟨by nlinarith, ho⟩
      · rintro (h | ⟨h, ho⟩)
        · exact Or.inl (by nlinarith)
        · exact Or.inr ⟨by nlinarith, ho⟩
    rw [criterion]
    constructor
    · intro hc
      have bound : S ≤ chi ^ a.r * D := by rcases hc with h | ⟨h, _⟩ <;> linarith
      have cap : a.r ≤ K := by
        by_contra hcap
        have hkr : K + 1 ≤ a.r := by omega
        have ckr : chi ^ a.r ≤ chi ^ (K + 1) :=
          pow_le_pow_of_le_one cp.le c1.le hkr
        have xa := mul_lt_mul_of_pos_left gap cKp
        have xz := mul_lt_mul_of_pos_left AZ cKp
        have xd := mul_lt_mul_of_pos_left hD.2 (pow_pos cp a.r)
        have xx := mul_le_mul_of_nonneg_right ckr Hp.le
        rw [pow_succ] at xx
        nlinarith
      refine ⟨cap, ?_⟩
      intro heq
      rw [heq, Sd] at hc
      cases ho : o 0 <;> simp only [ho, Bool.not_false, Bool.not_true, Bool.true_eq,
        if_true, Bool.false_eq_true, if_false] at *
      · rcases hc with h | ⟨_, h⟩
        · nlinarith only [h, cKp]
        · contradiction
      · rcases hc with h | ⟨h, _⟩ <;> nlinarith only [h, cKp]
    · rintro ⟨hr, hg⟩
      by_cases heq : a.r = K
      · rw [heq, Sd]
        cases ho : o 0 <;> simp only [ho, Bool.not_false, Bool.not_true, Bool.true_eq,
          if_true, Bool.false_eq_true, if_false] at hg
        · exact Or.inl (mul_lt_mul_of_pos_left (hg heq) cKp)
        · rcases lt_or_eq_of_le (hg heq) with h | h
          · exact Or.inl (mul_lt_mul_of_pos_left h cKp)
          · exact Or.inr ⟨by rw [h], rfl⟩
      · have rle : a.r ≤ K - 1 := by omega
        have cr : chi ^ (K - 1) ≤ chi ^ a.r :=
          pow_le_pow_of_le_one cp.le c1.le rle
        have pk : chi ^ K = chi ^ (K - 1) * chi := by
          rw [← pow_succ]; congr 1; omega
        have x := mul_lt_mul_of_pos_left hD.1 (pow_pos cp (K - 1))
        have y := mul_lt_mul_of_pos_left gap (pow_pos cp (K - 1))
        have z := mul_le_mul_of_nonneg_right cr Dp.le
        rw [pk] at SH
        exact Or.inl (by nlinarith)
  have controlGuard (xs : List Return) (D : ℝ) (hD : A < D ∧ D < H) :
      ClosedControl .high o b xs D ↔ GuardTrace K d (!o 0) .high xs D := by
    induction xs generalizing D with
    | nil => simp [ClosedControl, GuardTrace]
    | cons a xs ih =>
      change (condition .high (chi ^ a.r * D) ∧
        ClosedControl .high o b xs (returnMap .high a D)) ↔ _
      rw [scalar a D hD, ih _ (returnInterval a D hD)]
      exact and_assoc
  have fullD : A < execute .high execution (initial .high model) ∧
      execute .high execution (initial .high model) < H := by
    simpa only [List.take_length] using boundary.1 .high execution.length
  have startD : A < initial .high model ∧ initial .high model < H := by
    simpa only [List.take_zero, execute] using boundary.1 .high 0
  have tailD : A < xSide .high := by
    have h := (actual_complete_boundary_geometry .original []).1 .high 0
    simpa only [List.take_nil, execute, initial] using h.1
  rw [costs]
  have hsupply : condition .high (chi * execute .high execution (initial .high model)) :=
    Or.inl (by simpa only [mul_assoc] using auto _ fullD.1)
  have hasupply : condition .high (chi * xSide .high) := Or.inl (by simpa only [mul_assoc] using auto _ tailD)
  simp only [hsupply, hasupply, implies_true, true_and]
  exact controlGuard execution _ startD

set_option maxHeartbeats 1200000 in
-- Finite reset selection and arbitrary-list strict guard transfer share this proof.
/-- One paid actual reset works for both starts and makes every old weak guard
strict. An extra u after the first visible return also dominates its output,
including when that return is low; this is a separate protection. -/
theorem actual_reset_first_return (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K))) :
    ∃ R : Return, R.r = 1 ∧
      let B := hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high)
      max (max (xSide .high) (ySide .high)) ((lam - b) / g ^ 2 / chi ^ K) < B ∧
      (∀ D : ℝ, aSide .high < D → B < returnMap .high R D) ∧
      (∀ D : ℝ, aSide .high ≤ D → B ≤ returnMap .high R D) ∧
      (∀ (sourceModel targetModel : Model) (xs : List Return),
        GuardTrace K ((lam - b) / g ^ 2 / chi ^ K) false .high xs
          (initial .high sourceModel) →
        ActualPairSupply targetModel o b .strict (R :: xs)) ∧
      (∀ xs : List Return, listWeight (R :: xs) = 20 + 6 * R.m + listWeight xs) ∧
      (∀ (m r : ℕ) (z : ℝ), 1 ≤ m → 1 ≤ r → r ≤ K → aSide .high ≤ z →
        let difference :=
          (hSide .high - rho ^ (m + 1) * (hSide .high - chi ^ r * z)) -
          (hSide .high - rho ^ m * (hSide .high - chi ^ r * hSide .high))
        difference = rho ^ m *
          (aSide .high - chi ^ r * hSide .high + rho * chi ^ r * z) ∧
        0 < difference) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have root : g ^ 2 + 4 * g = 1 := by dsimp [g, t]; nlinarith
  have gp : 0 < g := by dsimp [g, t]; nlinarith
  have gq : g < 1 / 4 := by nlinarith
  have rp : 0 < rho := pow_pos gp 6
  have cp : 0 < chi := pow_pos gp 20
  have rb : rho < 1 / 4096 := by
    have h := pow_lt_pow_left₀ gq gp.le (by decide : (6 : ℕ) ≠ 0)
    norm_num [rho] at h ⊢; exact h
  have cb : chi < 1 / 256 := by
    have h20 : chi ≤ g ^ 4 := pow_le_pow_of_le_one gp.le (by linarith) (by decide)
    have h4 := pow_lt_pow_left₀ gq gp.le (by decide : (4 : ℕ) ≠ 0)
    norm_num at h4
    exact lt_of_le_of_lt h20 h4
  have r1 : rho < 1 := by linarith
  have c1 : chi < 1 := by linarith
  let H := hSide .high
  let A := aSide .high
  let d := (lam - b) / g ^ 2 / chi ^ K
  have Hp : 0 < H := by dsimp [H, hSide]; linarith
  have Ap : 0 < A := mul_pos (sub_pos.mpr r1) Hp
  have AH : A < H := by
    have h := mul_pos rp Hp
    dsimp [A, aSide, H] at *; nlinarith
  have gap : chi * H < A := by
    exact mul_lt_mul_of_pos_right (show chi < 1 - rho by linarith) Hp
  have cKp : 0 < chi ^ K := pow_pos cp K
  have g2p : 0 < g ^ 2 := pow_pos gp 2
  have dH : d < H := by
    apply (div_lt_iff₀ cKp).mpr
    apply (div_lt_iff₀ g2p).mpr
    dsimp [H] at *; nlinarith only [hqb]
  have states (md : Model) : A < initial .high md ∧ initial .high md < H := by
    simpa only [List.take_nil, execute] using
      (actual_complete_boundary_geometry md []).1 .high 0
  let L := max (max (xSide .high) (ySide .high)) d
  have LH : L < H := by
    exact max_lt (max_lt (states .original).2 (states .anchored).2) dH
  have factor : 0 < H - chi * A := by
    have h := mul_lt_mul_of_pos_left AH cp
    have hh : chi * H < H := by simpa only [one_mul] using mul_lt_mul_of_pos_right c1 Hp
    linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos (sub_pos.mpr LH) factor) r1
  let R : Return := ⟨n + 1, 1, by omega, by decide⟩
  let B := H - rho ^ R.m * (H - chi * A)
  have small : rho ^ R.m < (H - L) / (H - chi * A) := by
    have hle : rho ^ (n + 1) ≤ rho ^ n :=
      pow_le_pow_of_le_one rp.le r1.le (by omega)
    exact lt_of_le_of_lt hle hn
  have LB : L < B := by
    have h := (lt_div_iff₀ factor).mp small
    dsimp [B]; linarith
  have outputStrict (D : ℝ) (hD : A < D) : B < returnMap .high R D := by
    have h := mul_pos (mul_pos (pow_pos rp R.m) cp) (sub_pos.mpr hD)
    dsimp [returnMap, R, B, H, A] at *; simp only [pow_one] at *; nlinarith
  have outputWeak (D : ℝ) (hD : A ≤ D) : B ≤ returnMap .high R D := by
    have h := mul_nonneg (mul_pos (pow_pos rp R.m) cp).le (sub_nonneg.mpr hD)
    dsimp [returnMap, R, B, H, A] at *; simp only [pow_one] at *; nlinarith
  have ordered (a : Return) (D E : ℝ) (hDE : D < E) :
      returnMap .high a D < returnMap .high a E := by
    have h := mul_pos (mul_pos (pow_pos rp a.m) (pow_pos cp a.r)) (sub_pos.mpr hDE)
    dsimp [returnMap]; nlinarith
  have improve (xs : List Return) (D E : ℝ) (hDE : D < E)
      (hw : GuardTrace K d false .high xs D) : GuardTrace K d true .high xs E := by
    induction xs generalizing D E with
    | nil => trivial
    | cons a xs ih =>
      refine ⟨hw.1, ?_, ih _ _ (ordered a D E hDE) hw.2.2⟩
      intro heq
      have h := hw.2.1 heq
      simp only [Bool.false_eq_true, if_false] at h
      simp only [if_true]; linarith
  refine ⟨R, rfl, LB, outputStrict, outputWeak, ?_, ?_, ?_⟩
  · intro src dst xs hw
    have BD : initial .high src < B := by
      have hl : initial .high src ≤ L := by
        cases src
        · exact le_trans (le_max_left _ _) (le_max_left _ _)
        · exact le_trans (le_max_right _ _) (le_max_left _ _)
      exact lt_of_le_of_lt hl LB
    have first := outputStrict _ (states dst).1
    have trace : GuardTrace K d true .high (R :: xs) (initial .high dst) := by
      refine ⟨by dsimp [R]; omega, ?_, improve xs _ _ (lt_trans BD first) hw⟩
      intro heq; dsimp [R] at heq; omega
    exact (actual_strict_record_supply dst o b (R :: xs) K hK hqb hbp).1.mpr trace
  · intro xs
    simp only [listWeight, R]; omega
  · intro m r z hm hr hrK hz
    dsimp only
    have cr : chi ^ r ≤ chi := by
      simpa only [pow_one] using pow_le_pow_of_le_one cp.le c1.le hr
    have ch : chi ^ r * H < A :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right cr Hp.le) gap
    have zp : 0 < z := lt_of_lt_of_le Ap hz
    have zz : 0 ≤ rho * chi ^ r * z :=
      (mul_pos (mul_pos rp (pow_pos cp r)) zp).le
    have brace : 0 < A - chi ^ r * H + rho * chi ^ r * z := by linarith
    have identity :
        (H - rho ^ (m + 1) * (H - chi ^ r * z)) -
          (H - rho ^ m * (H - chi ^ r * H)) =
        rho ^ m * (A - chi ^ r * H + rho * chi ^ r * z) := by
      dsimp [A, aSide, H]; rw [pow_succ]; ring
    refine ⟨identity, ?_⟩
    rw [identity]; exact mul_pos (pow_pos rp m) brace


end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply
