/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion
   generality: G
   anchors: []
   utility: none
   digest: Actual Fibonacci complete boundaries constrain their occurrence inputs. -/

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

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

set_option maxHeartbeats 1000000 in
-- Uniform comparisons cover both starts, every prefix and all internal powers.
/-- Complete boundaries of both actual starts and the internal C/T inputs of the
same execution prefixes. Only complete boundaries have the lower bound A. -/
theorem actual_complete_boundary_geometry (model : Model) (execution : List Return) :
    (∀ (j : Side) (p : ℕ),
      aSide j < execute j (execution.take p) (initial j model) ∧
      execute j (execution.take p) (initial j model) < hSide j) ∧
    (∀ p : ℕ, execute .high (execution.take p) (initial .high model) <
      execute .low (execution.take p) (initial .low model)) ∧
    (∀ (j : Side) (p n k : ℕ),
      let D := execute j (execution.take p) (initial j model)
      let z := hSide j - rho ^ k * (hSide j - chi ^ n * D)
      0 < z ∧ z < hSide j ∧
      0 ≤ c0 + sign j * z ∧ c0 + sign j * z ≤ T2) ∧
    (∀ (p n k : ℕ),
      hSide .high - rho ^ k * (hSide .high - chi ^ n *
        execute .high (execution.take p) (initial .high model)) <
      hSide .low - rho ^ k * (hSide .low - chi ^ n *
        execute .low (execution.take p) (initial .low model))) ∧
    (∀ (j : Side) (p : ℕ),
      coordinate (sourcePrefix j model execution)
        ((stem j).length + listWeight (execution.drop p)) =
      c0 + sign j * execute j (execution.take p) (initial j model)) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsn := Real.sqrt_nonneg (5 : ℝ)
  have root : g ^ 2 + 4 * g = 1 := by dsimp [g, t]; nlinarith
  have gp : 0 < g := by dsimp [g, t]; nlinarith
  have gq : g < 1 / 4 := by nlinarith
  have tg : t = (1 + g) / 2 := by dsimp [g]; ring
  have rp : 0 < rho := pow_pos gp 6
  have cp : 0 < chi := pow_pos gp 20
  have rb : rho < 1 / 4096 := by
    have h := pow_lt_pow_left₀ gq gp.le (by decide : (6 : ℕ) ≠ 0)
    norm_num [rho] at h ⊢
    exact h
  have cb : chi < 1 / 256 := by
    have h20 : g ^ 20 ≤ g ^ 4 :=
      pow_le_pow_of_le_one gp.le (by linarith) (by decide)
    have h4 := pow_lt_pow_left₀ gq gp.le (by decide : (4 : ℕ) ≠ 0)
    norm_num at h4
    exact lt_of_le_of_lt h20 h4
  have r1 : rho < 1 := by linarith
  have c1 : chi < 1 := by linarith
  have hb (j : Side) : 1 / 16 < hSide j ∧ hSide j < eSide j ∧
      0 < eSide j ∧ eSide j < 1 := by
    cases j <;> dsimp [hSide, eSide, c0, T2] <;> simp only [tg] <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [gp, gq]
  have ap (j : Side) : 0 < aSide j := by
    exact mul_pos (sub_pos.mpr r1) (by linarith [(hb j).1])
  have ah (j : Side) : aSide j < hSide j := by
    have := mul_pos rp (by linarith [(hb j).1] : 0 < hSide j)
    dsimp [aSide]; nlinarith
  have ceA (j : Side) : chi * eSide j < aSide j := by
    have hcE := mul_lt_mul_of_pos_left (hb j).2.2.2 cp
    have hAh := mul_lt_mul_of_pos_right (show (3 / 4 : ℝ) < 1 - rho by linarith)
      (show 0 < hSide j by linarith [(hb j).1])
    dsimp [aSide] at *
    nlinarith [(hb j).1]
  have xp (j : Side) : aSide j < xSide j ∧ xSide j < hSide j := by
    have c3p : 0 < chi ^ 3 := pow_pos cp 3
    have c3le : chi ^ 3 ≤ chi := by
      simpa only [pow_one] using
        (pow_le_pow_of_le_one cp.le c1.le (by decide : 1 ≤ (3 : ℕ)))
    have c3E : chi ^ 3 * eSide j < hSide j :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right c3le (hb j).2.2.1.le)
        (lt_trans (ceA j) (ah j))
    have hpos := mul_pos rp (mul_pos c3p (hb j).2.2.1)
    have hgap := mul_pos rp (sub_pos.mpr c3E)
    dsimp [xSide, aSide] at *
    constructor <;> nlinarith
  have step (j : Side) (a : Return) (D : ℝ) (hD : aSide j < D ∧ D < hSide j) :
      aSide j < returnMap j a D ∧ returnMap j a D < hSide j := by
    have Dp : 0 < D := lt_trans (ap j) hD.1
    have cm := pow_pos cp a.r
    have rm := pow_pos rp a.m
    have cle : chi ^ a.r ≤ 1 := pow_le_one₀ cp.le c1.le
    have rle : rho ^ a.m ≤ rho := by
      simpa only [pow_one] using
        (pow_le_pow_of_le_one rp.le r1.le a.m_pos)
    have cd : chi ^ a.r * D < hSide j :=
      lt_of_le_of_lt (by nlinarith) hD.2
    have gap : 0 < hSide j - chi ^ a.r * D := sub_pos.mpr cd
    have gain := mul_pos rp (mul_pos cm Dp)
    have upper := mul_pos rm gap
    have lower := mul_le_mul_of_nonneg_right rle gap.le
    dsimp [returnMap, aSide] at *
    constructor <;> nlinarith
  have ip (j : Side) (md : Model) : aSide j < initial j md ∧ initial j md < hSide j := by
    cases md with
    | original => exact xp j
    | anchored =>
      have h := step j ⟨1, 1, by decide, by decide⟩ (xSide j) (xp j)
      dsimp [initial, returnMap, ySide, aSide] at h ⊢
      constructor <;> nlinarith only [h.1, h.2]
  have hh : hSide .high < hSide .low := by dsimp [hSide]; linarith
  have ee : eSide .high < eSide .low := by dsimp [eSide, c0, T2]; rw [tg]; nlinarith
  have xx : xSide .high < xSide .low := by
    have ha := mul_pos (sub_pos.mpr r1) (sub_pos.mpr hh)
    have hx := mul_pos (mul_pos rp (pow_pos cp 3)) (sub_pos.mpr ee)
    dsimp [xSide, aSide] at *; nlinarith
  have ordered (a : Return) (DH DL : ℝ) (hD : DH < DL) :
      returnMap .high a DH < returnMap .low a DL := by
    have rm := pow_pos rp a.m
    have cm := pow_pos cp a.r
    have rlt := pow_lt_one₀ rp.le r1 (Nat.ne_of_gt a.m_pos)
    have hhg := mul_pos (sub_pos.mpr rlt) (sub_pos.mpr hh)
    have hdg := mul_pos (mul_pos rm cm) (sub_pos.mpr hD)
    dsimp [returnMap]; nlinarith
  have io (md : Model) : initial .high md < initial .low md := by
    cases md with
    | original => exact xx
    | anchored =>
      have h := ordered ⟨1, 1, by decide, by decide⟩ _ _ xx
      dsimp [initial, returnMap, ySide, aSide] at h ⊢
      nlinarith only [h]
  have run (j : Side) (xs : List Return) (D : ℝ)
      (hD : aSide j < D ∧ D < hSide j) :
      aSide j < execute j xs D ∧ execute j xs D < hSide j := by
    induction xs generalizing D with
    | nil => exact hD
    | cons a rest ih => exact ih _ (step j a D hD)
  have runOrder (xs : List Return) (DH DL : ℝ) (hD : DH < DL) :
      execute .high xs DH < execute .low xs DL := by
    induction xs generalizing DH DL with
    | nil => exact hD
    | cons a rest ih => exact ih _ _ (ordered a DH DL hD)
  refine ⟨fun j p => run j (execution.take p) _ (ip j model),
    fun p => runOrder (execution.take p) _ _ (io model), ?_, ?_, ?_⟩
  · intro j p n k
    dsimp only
    let D := execute j (execution.take p) (initial j model)
    change 0 < hSide j - rho ^ k * (hSide j - chi ^ n * D) ∧
      hSide j - rho ^ k * (hSide j - chi ^ n * D) < hSide j ∧
      0 ≤ c0 + sign j * (hSide j - rho ^ k * (hSide j - chi ^ n * D)) ∧
      c0 + sign j * (hSide j - rho ^ k * (hSide j - chi ^ n * D)) ≤ T2
    have hD := run j (execution.take p) _ (ip j model)
    change aSide j < D ∧ D < hSide j at hD
    have Dp := lt_trans (ap j) hD.1
    have cn := pow_pos cp n
    have rk := pow_pos rp k
    have cnle : chi ^ n ≤ 1 := pow_le_one₀ cp.le c1.le
    have rkle : rho ^ k ≤ 1 := pow_le_one₀ rp.le r1.le
    have z0 := mul_pos cn Dp
    have zh : chi ^ n * D < hSide j := lt_of_le_of_lt (by nlinarith) hD.2
    have zgap := mul_pos rk (sub_pos.mpr zh)
    have zl := mul_le_mul_of_nonneg_right rkle (sub_pos.mpr zh).le
    have zpos : 0 < hSide j - rho ^ k * (hSide j - chi ^ n * D) := by nlinarith
    have zhi : hSide j - rho ^ k * (hSide j - chi ^ n * D) < hSide j := by linarith
    refine ⟨zpos, zhi, ?_, ?_⟩
    all_goals have zE := lt_trans zhi (hb j).2.1
    all_goals cases j <;> dsimp [sign, eSide, c0, T2] at zE zpos ⊢ <;>
      simp only [tg] at zE zpos ⊢ <;> nlinarith
  · intro p n k
    have hd := runOrder (execution.take p) _ _ (io model)
    have cn := pow_pos cp n
    have rk := pow_pos rp k
    have rk1 : rho ^ k ≤ 1 := pow_le_one₀ rp.le r1.le
    have hgap := mul_nonneg (sub_nonneg.mpr rk1) (sub_pos.mpr hh).le
    have dgap := mul_pos (mul_pos rk cn) (sub_pos.mpr hd)
    nlinarith

  · intro j p
    have extLength (xs : List Return) : (externalWord j xs).length = listWeight xs := by
      have hl := (paired_source_reconstruction j .original xs).2.2.2.2.1
      have hst : (stem j).length = 26 := by cases j <;> rfl
      simp only [observedPrefix, List.length_append, anchor, List.length_nil,
        observationOffset, hst, Nat.add_zero] at hl
      exact Nat.add_left_cancel hl
    have extSplit : externalWord j execution =
        externalWord j (execution.drop p) ++ externalWord j (execution.take p) := by
      calc
        externalWord j execution = externalWord j (execution.take p ++ execution.drop p) :=
          congrArg (externalWord j) (List.take_append_drop p execution).symm
        _ = externalWord j (execution.drop p) ++ externalWord j (execution.take p) := by
          simp only [externalWord, List.reverse_append, List.map_append, List.flatten_append]
    have sourceSplit : sourcePrefix j model execution =
        (stem j ++ externalWord j (execution.drop p)) ++
        (externalWord j (execution.take p) ++ anchor j model ++ tailPrefix j) := by
      simp only [sourcePrefix, observedPrefix, extSplit, List.append_assoc]
    have index : (stem j).length + listWeight (execution.drop p) =
        (stem j ++ externalWord j (execution.drop p)).length := by
      simp only [List.length_append, extLength]
    rw [coordinate, sourceSplit, index]
    simp only [List.drop_append, List.drop_eq_nil_of_le le_rfl, Nat.sub_self,
      List.drop_zero, List.nil_append, Nat.zero_sub]
    simpa only [coordinate, List.drop_zero] using
      (paired_source_reconstruction j model (execution.take p)).2.2.2.1


/-- Exact active costs, evaluated on one execution from its fixed literal tail. -/
def StrictControl (j : Side) (b : ℝ) : List Return → ℝ → Prop
  | [], _ => True
  | a :: rest, D => lam - g ^ 2 * chi ^ a.r * D < b ∧
      StrictControl j b rest (returnMap j a D)

set_option maxHeartbeats 1600000 in
-- Repeated blocks and all-source errors are constructed in one live proof.
/-- Every finite departure error is assembled on the prescribed source. The
stem and paid anchor are included; the terminal future is read with zero error. -/
theorem actual_strict_record_supply (model : Model) (o : Ownership) (b : ℝ)
    (execution : List Return) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K))) :
    (ActualPairSupply model o b .strict execution ↔
      GuardTrace K ((lam - b) / g ^ 2 / chi ^ K) true .high execution
        (initial .high model)) ∧
    (ActualPairSupply model o b .recordMargin execution ↔
      GuardTrace K ((lam - b) / g ^ 2 / chi ^ K) true .high execution
        (initial .high model)) := by
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
  have app := literal_source_geometry.2.2.2.2
  have appendSupply (w v : List Label) (cs ds : List Color) (z : ℝ)
      (len : w.length = cs.length) :
      BlockSupply o b true (w ++ v) (cs ++ ds) z ↔
        BlockSupply o b true w cs (compose v z) ∧ BlockSupply o b true v ds z := by
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
      BlockSupply o b true (repeatWord (block j) n)
        (List.replicate n colorsD).flatten (c0 + sign j * D) ↔
      (0 < n → lam - g ^ 2 * D < b) := by
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
      rw [(literal_full_slot_readout o b hb).1 j _ dn.1 (le_of_lt (lt_trans dn.2 (hp j).2)), ih]
      have lower : D ≤ hSide j - rho ^ n * (hSide j - D) := by
        have rl : rho ^ n ≤ 1 := pow_le_one₀ rp.le r1.le
        have gl := mul_le_mul_of_nonneg_right rl (sub_pos.mpr hD.2).le
        linarith
      have gg : 0 < g ^ 2 := pow_pos gp 2
      constructor
      · rintro ⟨houter, hinner⟩ _
        cases n with
        | zero => simpa using houter
        | succ n => exact hinner (by omega)
      · intro h
        constructor
        · have hc := mul_le_mul_of_nonneg_left lower gg.le
          have hbase := h (by omega)
          nlinarith
        · intro _; exact h (by omega)
  have twenty (j : Side) (n : ℕ) (D : ℝ) (hD : 0 < D ∧ D < hSide j) :
      BlockSupply o b true (repeatWord C n)
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
      exact (literal_full_slot_readout o b hb).2.2 _ (domain j _ dn).1 (domain j _ dn).2
  have returns (j : Side) (a : Return) (D : ℝ) (hD : 0 < D ∧ D < hSide j) :
      BlockSupply o b true (returnWord j a) (returnColors a) (c0 + sign j * D) ↔
        lam - g ^ 2 * chi ^ a.r * D < b := by
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
    simp only [a.m_pos, forall_const, twenty j a.r D hD, and_true, mul_assoc]
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
      BlockSupply o b true (stem j) (colorsD ++ colorsE) (c0 + sign j * D) ↔
        lam - g ^ 2 * chi * D < b := by
    have h := returns j ⟨1, 1, by decide, by decide⟩ D hD
    simpa only [returnWord, returnColors, repeatWord, List.append_nil,
      List.replicate_succ, List.replicate_zero, List.flatten_cons, List.flatten_nil,
      stem, pow_one] using h
  have pairErrors : ActualPairSupply model o b .strict execution ↔
      ∀ j : Side, BlockSupply o b true (observedPrefix j model execution)
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
        · simpa using bp
      · intro p hp
        dsimp [err]; rw [dif_pos hp, coord j p hp]
        exact (Classical.choose_spec (h j p hp)).2
      · intro p hp; dsimp [err]; rw [dif_neg (by omega)]
      · intro p
        have hz : err ((observedPrefix j model execution).length + p) = 0 := by
          dsimp [err]; rw [dif_neg (by rw [lengthEq]; omega)]
        rw [hz, (paired_source_reconstruction j model execution).2.2.1]
  have costs : ActualPairSupply model o b .strict execution ↔
      lam - g ^ 2 * chi * execute .high execution (initial .high model) < b ∧
      (model = .anchored → lam - g ^ 2 * chi * xSide .high < b) ∧
      StrictControl .high b execution (initial .high model) := by
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
        BlockSupply o b true (externalWord j xs) (xs.reverse.map returnColors).flatten
          (c0 + sign j * D) ↔ StrictControl j b xs D := by
      induction xs generalizing D with
      | nil => simp [externalWord, BlockSupply, StrictControl]
      | cons a xs ih =>
        simp only [externalWord, List.reverse_cons, List.map_append, List.map_cons,
          List.map_nil, List.flatten_append, List.flatten_cons, List.flatten_nil,
          List.append_nil]
        change BlockSupply o b true (externalWord j xs ++ returnWord j a)
          ((xs.reverse.map returnColors).flatten ++ returnColors a) (c0 + sign j * D) ↔
          StrictControl j b (a :: xs) D
        rw [appendSupply _ _ _ _ _ (extLen j xs),
          (paired_source_reconstruction j .original []).2.2.2.2.2.2.2.2.1,
          ih _ (returnDomain j a D hD), returns j a D hD]
        change (StrictControl j b xs (returnMap j a D) ∧
          lam - g ^ 2 * chi ^ a.r * D < b) ↔
          (lam - g ^ 2 * chi ^ a.r * D < b ∧ StrictControl j b xs (returnMap j a D))
        exact and_comm
    have anchorTail (j : Side) : compose (anchor j model) (coordinate (tailPrefix j) 0) =
        c0 + sign j * initial j model := by
      have h := (paired_source_reconstruction j model []).2.2.2.1
      simpa only [externalWord, List.reverse_nil, List.map_nil, List.flatten_nil,
        List.nil_append, coordinate, List.drop_zero, app, execute] using h
    have anchorSupply (j : Side) (md : Model) :
        BlockSupply o b true (anchor j md)
          (match md with | .original => [] | .anchored => colorsD ++ colorsE)
          (coordinate (tailPrefix j) 0) ↔
        (md = .anchored → lam - g ^ 2 * chi * xSide j < b) := by
      have tail := (paired_source_reconstruction j .original []).2.2.2.2.2.2.2.2.2.2
      cases md with
      | original => simp [anchor, BlockSupply]
      | anchored =>
        simp only [anchor, coordinate, List.drop_zero, tail, true_implies]
        exact stemSupply j (xSide j) (initialDomain j .original)
    have wholeSide (j : Side) :
        BlockSupply o b true (observedPrefix j model execution) (history model execution)
          (coordinate (tailPrefix j) 0) ↔
        lam - g ^ 2 * chi * execute j execution (initial j model) < b ∧
        (model = .anchored → lam - g ^ 2 * chi * xSide j < b) ∧
        StrictControl j b execution (initial j model) := by
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
        (hc : StrictControl .high b xs DH) : StrictControl .low b xs DL := by
      induction xs generalizing DH DL with
      | nil => trivial
      | cons a xs ih =>
        refine ⟨?_, ih _ _ (returnOrder a DH DL ho) hc.2⟩
        have gain := mul_pos (mul_pos (pow_pos gp 2) (pow_pos cp a.r)) (sub_pos.mpr ho)
        have h := hc.1; nlinarith
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
        · nlinarith
        · intro hm; have h := hanchor hm; nlinarith
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
      lam - g ^ 2 * chi ^ a.r * D < b ↔
      a.r ≤ K ∧ (a.r = K → d < D) := by
    have Dp : 0 < D := lt_trans Ap hD.1
    have criterion : lam - g ^ 2 * chi ^ a.r * D < b ↔ S < chi ^ a.r * D := by
      rw [div_lt_iff₀ g2p]
      constructor <;> intro h <;> nlinarith
    rw [criterion]
    constructor
    · intro hc
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
      nlinarith only [hc, cKp]
    · rintro ⟨hr, hg⟩
      by_cases heq : a.r = K
      · rw [heq, Sd]; exact mul_lt_mul_of_pos_left (hg heq) cKp
      · have rle : a.r ≤ K - 1 := by omega
        have cr : chi ^ (K - 1) ≤ chi ^ a.r :=
          pow_le_pow_of_le_one cp.le c1.le rle
        have pk : chi ^ K = chi ^ (K - 1) * chi := by
          rw [← pow_succ]; congr 1; omega
        have x := mul_lt_mul_of_pos_left hD.1 (pow_pos cp (K - 1))
        have y := mul_lt_mul_of_pos_left gap (pow_pos cp (K - 1))
        have z := mul_le_mul_of_nonneg_right cr Dp.le
        rw [pk] at SH
        nlinarith
  have controlGuard (xs : List Return) (D : ℝ) (hD : A < D ∧ D < H) :
      StrictControl .high b xs D ↔ GuardTrace K d true .high xs D := by
    induction xs generalizing D with
    | nil => simp [StrictControl, GuardTrace]
    | cons a xs ih =>
      simp only [StrictControl, GuardTrace, Bool.true_eq, if_true]
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
  have strictCap : ActualPairSupply model o b .strict execution ↔
      GuardTrace K ((lam - b) / g ^ 2 / chi ^ K) true .high execution
        (initial .high model) := by
    rw [costs]
    have hsupply := auto _ fullD.1
    have hasupply := auto _ tailD
    simp only [hsupply, hasupply, implies_true, true_and]
    exact controlGuard execution _ startD
  have marginStrict : ActualPairSupply model o b .recordMargin execution ↔
      ActualPairSupply model o b .strict execution := by
    constructor
    · intro h j
      obtain ⟨err, ⟨eps, heps, herr⟩, hread, hzero, hfuture⟩ := h j
      refine ⟨err, ?_, hread, hzero, hfuture⟩
      intro p
      have h := herr p
      linarith
    · intro h j
      obtain ⟨err, herr, hread, hzero, hfuture⟩ := h j
      have finiteGap (n : ℕ) :
          ∃ eps > 0, eps ≤ b ∧ ∀ p, p < n → |err p| ≤ b - eps := by
        induction n with
        | zero =>
          refine ⟨b / 2, by linarith, by linarith, ?_⟩
          intro p hp; omega
        | succ n ih =>
          obtain ⟨eps, heps, heb, hgap⟩ := ih
          let delta : ℝ := min eps ((b - |err n|) / 2)
          have hn := herr n
          have dp : 0 < delta := lt_min heps (by linarith)
          have de : delta ≤ eps := min_le_left _ _
          have dn : delta ≤ (b - |err n|) / 2 := min_le_right _ _
          refine ⟨delta, dp, le_trans de heb, ?_⟩
          intro p hp
          by_cases hpold : p < n
          · have hh := hgap p hpold; linarith
          · have pn : p = n := by omega
            rw [pn]; linarith
      obtain ⟨eps, heps, heb, hgap⟩ := finiteGap (history model execution).length
      refine ⟨err, ⟨eps, heps, ?_⟩, hread, hzero, hfuture⟩
      intro p
      by_cases hp : p < (history model execution).length
      · exact hgap p hp
      · rw [hzero p (by omega), abs_zero]
        linarith
  exact ⟨strictCap, marginStrict.trans strictCap⟩

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

/-- Execution letters are distinct from literal source labels and colors. -/
inductive CuLetter | c | u
  deriving DecidableEq, Repr

instance : Fintype CuLetter where
  elems := {CuLetter.c, CuLetter.u}
  complete a := by cases a <;> simp

instance : TopologicalSpace CuLetter := ⊥
instance : DiscreteTopology CuLetter := ⟨rfl⟩

def isC : CuLetter → Bool | CuLetter.c => true | CuLetter.u => false
def isU : CuLetter → Bool | CuLetter.c => false | CuLetter.u => true

def executionWord : List Return → List CuLetter
  | [] => []
  | a :: xs => List.replicate a.r CuLetter.c ++ List.replicate a.m CuLetter.u ++ executionWord xs

def wordWeight : List CuLetter → ℕ
  | [] => 0
  | CuLetter.c :: xs => 20 + wordWeight xs
  | CuLetter.u :: xs => 6 + wordWeight xs

set_option maxHeartbeats 600000 in
-- Maximal initial runs recover both positive return exponents before recursion.
/-- Complete execution words have canonical maximal c/u runs. Their run counts
recover the positive return list uniquely and preserve the original 20/6 weight. -/
theorem complete_execution_word_parser :
    (∀ (a : Return) (xs : List Return),
      (executionWord (a :: xs)).takeWhile isC = List.replicate a.r CuLetter.c) ∧
    (∀ (a : Return) (xs : List Return),
      ((executionWord (a :: xs)).drop a.r).takeWhile isU = List.replicate a.m CuLetter.u) ∧
    Function.Injective executionWord ∧
    (∀ xs : List Return, wordWeight (executionWord xs) = listWeight xs) ∧
    (∀ model : Model, Function.Injective (history model)) := by
  have headU (xs : List Return) : (executionWord xs).takeWhile isU = [] := by
    cases xs with
    | nil => rfl
    | cons a xs =>
      cases hr : a.r with
      | zero => have h := a.r_pos; omega
      | succ r => simp [executionWord, hr, List.replicate_succ, List.takeWhile_cons, isU]
  have cprefix (n : ℕ) (rest : List CuLetter) :
      (List.replicate n CuLetter.c ++ CuLetter.u :: rest).takeWhile isC = List.replicate n CuLetter.c := by
    induction n with
    | zero => simp [List.takeWhile_cons, isC]
    | succ n ih => simp [List.replicate_succ, List.takeWhile_cons, isC, ih]
  have uprefix (n : ℕ) (xs : List Return) :
      (List.replicate n CuLetter.u ++ executionWord xs).takeWhile isU = List.replicate n CuLetter.u := by
    induction n with
    | zero => simpa using headU xs
    | succ n ih => simp [List.replicate_succ, List.takeWhile_cons, isU, ih]
  have firstC (a : Return) (xs : List Return) :
      (executionWord (a :: xs)).takeWhile isC = List.replicate a.r CuLetter.c := by
    cases hm : a.m with
    | zero => have h := a.m_pos; omega
    | succ m =>
      simpa only [executionWord, hm, List.replicate_succ, List.append_assoc,
        List.cons_append] using cprefix a.r (List.replicate m CuLetter.u ++ executionWord xs)
  have afterC (a : Return) (xs : List Return) :
      (executionWord (a :: xs)).drop a.r = List.replicate a.m CuLetter.u ++ executionWord xs := by
    simp [executionWord, List.append_assoc, List.drop_append]
  have firstU (a : Return) (xs : List Return) :
      ((executionWord (a :: xs)).drop a.r).takeWhile isU = List.replicate a.m CuLetter.u := by
    rw [afterC]; exact uprefix a.m xs
  have injective : Function.Injective executionWord := by
    intro xs
    induction xs with
    | nil =>
      intro ys heq
      cases ys with
      | nil => rfl
      | cons b ys =>
        have h := congrArg List.length heq
        simp only [executionWord, List.length_nil, List.length_append, List.length_replicate] at h
        have hr := b.r_pos; omega
    | cons a xs ih =>
      intro ys heq
      cases ys with
      | nil =>
        have h := congrArg List.length heq
        simp only [executionWord, List.length_nil, List.length_append, List.length_replicate] at h
        have hr := a.r_pos; omega
      | cons b ys =>
        have hr : a.r = b.r := by
          have h := congrArg (fun w : List CuLetter => (w.takeWhile isC).length) heq
          simpa only [firstC, List.length_replicate] using h
        have hu : List.replicate a.m CuLetter.u ++ executionWord xs =
            List.replicate b.m CuLetter.u ++ executionWord ys := by
          have h := congrArg (List.drop a.r) heq
          rw [afterC, hr, afterC] at h
          exact h
        have hm : a.m = b.m := by
          have h := congrArg (fun w : List CuLetter => (w.takeWhile isU).length) hu
          simpa only [uprefix, List.length_replicate] using h
        have htail : executionWord xs = executionWord ys := by
          rw [← hm] at hu
          exact List.append_cancel_left hu
        have hab : a = b := by cases a; cases b; simp_all
        exact congrArg₂ List.cons hab (ih htail)
  have appendWeight (w v : List CuLetter) : wordWeight (w ++ v) = wordWeight w + wordWeight v := by
    induction w with
    | nil => simp [wordWeight]
    | cons a w ih => cases a <;> simp [wordWeight, ih, Nat.add_assoc]
  have cweight (n : ℕ) : wordWeight (List.replicate n CuLetter.c) = 20 * n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, wordWeight, ih]; omega
  have uweight (n : ℕ) : wordWeight (List.replicate n CuLetter.u) = 6 * n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, wordWeight, ih]; omega
  let encode (w : List CuLetter) : List Color :=
    (w.map (fun l => match l with | .c => colorsE | .u => colorsD)).flatten
  have encodeAppend (w v : List CuLetter) : encode (w ++ v) = encode w ++ encode v := by
    induction w with
    | nil => simp [encode, executionWord]
    | cons a w ih => cases a <;> simp [encode, ih, List.append_assoc]
  have encodeRepC (n : ℕ) : encode (List.replicate n CuLetter.c) =
      (List.replicate n colorsE).flatten := by
    induction n with
    | zero => simp [encode]
    | succ n ih => simp [List.replicate_succ, encode, ih]
  have encodeRepU (n : ℕ) : encode (List.replicate n CuLetter.u) =
      (List.replicate n colorsD).flatten := by
    induction n with
    | zero => simp [encode]
    | succ n ih => simp [List.replicate_succ, encode, ih]
  have encodeInj : Function.Injective encode := by
    intro w
    induction w with
    | nil =>
      intro v heq
      cases v with
      | nil => simp [encode, executionWord]
      | cons y v => cases y <;> simp [encode, colorsD, colorsE] at heq
    | cons x w ih =>
      intro v heq
      cases v with
      | nil => cases x <;> simp [encode, colorsD, colorsE] at heq
      | cons y v =>
        cases x <;> cases y
        · have h : encode w = encode v := by
            exact List.append_cancel_left (by simpa only [encode, List.map_cons, List.flatten_cons] using heq)
          exact congrArg (List.cons CuLetter.c) (ih h)
        · have h := congrArg (fun l : List Color => l[1]?) heq
          simp [encode, colorsD, colorsE] at h
        · have h := congrArg (fun l : List Color => l[1]?) heq
          simp [encode, colorsD, colorsE] at h
        · have h : encode w = encode v := by
            exact List.append_cancel_left (by simpa only [encode, List.map_cons, List.flatten_cons] using heq)
          exact congrArg (List.cons CuLetter.u) (ih h)
  have externalEncoding (xs : List Return) : encode (executionWord xs).reverse =
      (xs.reverse.map returnColors).flatten := by
    induction xs with
    | nil => simp [encode, executionWord]
    | cons a xs ih =>
      simp [executionWord, List.reverse_append, List.reverse_replicate, encodeAppend,
        encodeRepC, encodeRepU, ih, List.reverse_cons, returnColors, List.append_assoc]
  refine ⟨firstC, firstU, injective, ?_, ?_⟩
  · intro xs
    induction xs with
    | nil => simp [executionWord, wordWeight, listWeight]
    | cons a xs ih =>
      simp [executionWord, appendWeight, cweight, uweight, ih, listWeight]; omega
  · intro model xs ys heq
    have h : (xs.reverse.map returnColors).flatten = (ys.reverse.map returnColors).flatten := by
      unfold history at heq
      exact List.append_cancel_left (List.append_cancel_right heq)
    have hc : encode (executionWord xs).reverse = encode (executionWord ys).reverse := by
      rw [externalEncoding, externalEncoding]; exact h
    have hr := encodeInj hc
    apply injective
    simpa only [List.reverse_reverse] using congrArg List.reverse hr

/-- The auxiliary letter dynamics use the original high-side constants. -/
noncomputable def letterMap : CuLetter → ℝ → ℝ
  | .c, z => chi * z
  | .u, z => aSide .high + rho * z

def letterWeight : CuLetter → ℕ | .c => 20 | .u => 6

/-- Compose exactly the last N letters before i, starting from the supplied seed. -/
noncomputable def finitePast (ω : ℤ → CuLetter) (i : ℤ) : ℕ → ℝ → ℝ
  | 0, z => z
  | N + 1, z => letterMap (ω (i - 1)) (finitePast ω (i - 1) N z)

def pastWeight (ω : ℤ → CuLetter) (i : ℤ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => letterWeight (ω (i - 1)) + pastWeight ω (i - 1) N

/-- A state defined by the finite zero-seed past, independently of actual records. -/
noncomputable def pastState (ω : ℤ → CuLetter) (i : ℤ) : ℝ :=
  ⨆ N : ℕ, finitePast ω i N 0

/-- The guard is checked before the current Kth c transition. -/
def AuxiliaryLanguage (K : ℕ) (d : ℝ) : Set (ℤ → CuLetter) :=
  {ω | (∀ i : ℤ, ¬ ∀ k : Fin (K + 1), ω (i + (k : ℕ)) = .c) ∧
    (∀ i : ℤ, (∀ k : Fin K, ω (i - (k : ℕ)) = .c) →
      chi ^ (K - 1) * d ≤ pastState ω i)}

def Occurs (ω : ℤ → CuLetter) (w : List CuLetter) : Prop :=
  ∃ i : ℤ, ∀ k : Fin w.length, ω (i + (k : ℕ)) = w[k]

def AuxiliaryFactor (K : ℕ) (d : ℝ) (w : List CuLetter) : Prop :=
  ∃ ω ∈ AuxiliaryLanguage K d, Occurs ω w

open Filter Topology in
set_option maxHeartbeats 1000000 in
/-- Finite pasts converge to the unique bounded bilateral trajectory. Exact
weighted contraction, arbitrary seeds and matching-past stability are derived
from the original letter maps. The all-u state is the original fixed point h. -/
theorem bilateral_past_state :
    (∀ (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ) (x y : ℝ),
      finitePast ω i N y - finitePast ω i N x = g ^ pastWeight ω i N * (y - x)) ∧
    (∀ (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ),
      0 ≤ g ^ pastWeight ω i N ∧ g ^ pastWeight ω i N ≤ rho ^ N) ∧
    (∀ (ω : ℤ → CuLetter) (i : ℤ),
      0 ≤ pastState ω i ∧ pastState ω i ≤ hSide .high) ∧
    (∀ (ω : ℤ → CuLetter) (i : ℤ) (z : ℝ), 0 ≤ z → z ≤ hSide .high →
      Tendsto (fun N : ℕ => finitePast ω i N z) atTop (𝓝 (pastState ω i))) ∧
    (∀ (ω : ℤ → CuLetter) (i : ℤ),
      pastState ω (i + 1) = letterMap (ω i) (pastState ω i)) ∧
    (∀ (ω : ℤ → CuLetter) (y : ℤ → ℝ),
      (∀ i, 0 ≤ y i ∧ y i ≤ hSide .high) →
      (∀ i, y (i + 1) = letterMap (ω i) (y i)) → y = pastState ω) ∧
    (∀ (ω ν : ℤ → CuLetter) (i : ℤ) (N : ℕ),
      (∀ k : Fin N, ω (i - 1 - (k : ℕ)) = ν (i - 1 - (k : ℕ))) →
      |pastState ω i - pastState ν i| ≤ hSide .high * rho ^ N) ∧
    (∀ i : ℤ, pastState (fun _ => CuLetter.u) i = hSide .high) ∧
    (∀ i : ℤ, Continuous (fun ω : ℤ → CuLetter => pastState ω i)) ∧
    (∀ (K : ℕ) (d : ℝ), 1 ≤ K →
      (AuxiliaryLanguage K d).Nonempty ∧ IsCompact (AuxiliaryLanguage K d)) ∧
    (∀ (ω : ℤ → CuLetter) (i j : ℤ),
      pastState (fun n => ω (n + j)) i = pastState ω (i + j)) ∧
    (∀ (ω : ℤ → CuLetter) (j : ℤ) (K : ℕ) (d : ℝ),
      ω ∈ AuxiliaryLanguage K d ↔ (fun n => ω (n + j)) ∈ AuxiliaryLanguage K d) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsn := Real.sqrt_nonneg (5 : ℝ)
  have root : g ^ 2 + 4 * g = 1 := by dsimp [g, t]; nlinarith
  have gp : 0 < g := by dsimp [g, t]; nlinarith
  have gq : g < 1 / 4 := by nlinarith
  have g1 : g < 1 := by linarith
  have rp : 0 < rho := pow_pos gp 6
  have cp : 0 < chi := pow_pos gp 20
  have r1 : rho < 1 := pow_lt_one₀ gp.le g1 (by decide : (6 : ℕ) ≠ 0)
  have cr : chi ≤ rho := pow_le_pow_of_le_one gp.le g1.le (by decide)
  have c1 : chi ≤ 1 := le_trans cr r1.le
  let H := hSide .high
  have Hp : 0 < H := by dsimp [H, hSide]; linarith
  have ap : 0 ≤ aSide .high := by dsimp [aSide]; exact mul_nonneg (sub_pos.mpr r1).le Hp.le
  have mapInterval (a : CuLetter) (z : ℝ) (hz : 0 ≤ z ∧ z ≤ H) :
      0 ≤ letterMap a z ∧ letterMap a z ≤ H := by
    cases a <;> dsimp [letterMap]
    · exact ⟨mul_nonneg cp.le hz.1, le_trans (mul_le_mul_of_nonneg_right c1 hz.1) (by simpa using hz.2)⟩
    · constructor
      · exact add_nonneg ap (mul_nonneg rp.le hz.1)
      · have h := mul_le_mul_of_nonneg_left hz.2 rp.le
        dsimp [aSide, H] at *; nlinarith
  have mapMono (a : CuLetter) : Monotone (letterMap a) := by
    intro x y hxy
    cases a <;> dsimp [letterMap]
    · exact mul_le_mul_of_nonneg_left hxy cp.le
    · exact add_le_add_right (mul_le_mul_of_nonneg_left hxy rp.le) _
  have interval (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ) (z : ℝ) (hz : 0 ≤ z ∧ z ≤ H) :
      0 ≤ finitePast ω i N z ∧ finitePast ω i N z ≤ H := by
    induction N generalizing i with
    | zero => exact hz
    | succ N ih => exact mapInterval _ _ (ih (i - 1))
  have difference (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ) (x y : ℝ) :
      finitePast ω i N y - finitePast ω i N x = g ^ pastWeight ω i N * (y - x) := by
    induction N generalizing i with
    | zero => simp [finitePast, pastWeight]
    | succ N ih =>
      simp only [finitePast, pastWeight, pow_add]
      cases ha : ω (i - 1) <;> simp only [ha, letterMap, letterWeight]
      · rw [← mul_sub, ih]; dsimp [chi]; ring
      · rw [add_sub_add_left_eq_sub, ← mul_sub, ih]; dsimp [rho]; ring
  have contraction (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ) :
      0 ≤ g ^ pastWeight ω i N ∧ g ^ pastWeight ω i N ≤ rho ^ N := by
    refine ⟨pow_nonneg gp.le _, ?_⟩
    induction N generalizing i with
    | zero => simp [pastWeight]
    | succ N ih =>
      rw [pastWeight, pow_add, pow_succ]
      have slope : g ^ letterWeight (ω (i - 1)) ≤ rho := by
        cases ω (i - 1) <;> simp only [letterWeight]
        · exact cr
        · rfl
      calc
        g ^ letterWeight (ω (i - 1)) * g ^ pastWeight ω (i - 1) N ≤ rho * rho ^ N :=
          mul_le_mul slope (ih (i - 1)) (pow_nonneg gp.le _) rp.le
        _ = rho ^ N * rho := mul_comm _ _
  have seedMono (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ) : Monotone (finitePast ω i N) := by
    induction N generalizing i with
    | zero => exact monotone_id
    | succ N ih => exact (mapMono _).comp (ih (i - 1))
  have zeroStep (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ) :
      finitePast ω i N 0 ≤ finitePast ω i (N + 1) 0 := by
    induction N generalizing i with
    | zero => exact (interval ω i 1 0 ⟨le_rfl, Hp.le⟩).1
    | succ N ih => exact mapMono _ (ih (i - 1))
  have zeroMono (ω : ℤ → CuLetter) (i : ℤ) : Monotone (fun N => finitePast ω i N 0) :=
    monotone_nat_of_le_succ (zeroStep ω i)
  have bounded (ω : ℤ → CuLetter) (i : ℤ) : BddAbove (Set.range (fun N => finitePast ω i N 0)) := by
    refine ⟨H, ?_⟩
    rintro _ ⟨N, rfl⟩; exact (interval ω i N 0 ⟨le_rfl, Hp.le⟩).2
  have zeroLimit (ω : ℤ → CuLetter) (i : ℤ) :
      Tendsto (fun N : ℕ => finitePast ω i N 0) atTop (𝓝 (pastState ω i)) :=
    tendsto_atTop_ciSup (zeroMono ω i) (bounded ω i)
  have stateInterval (ω : ℤ → CuLetter) (i : ℤ) : 0 ≤ pastState ω i ∧ pastState ω i ≤ H := by
    constructor
    · exact ge_of_tendsto' (zeroLimit ω i) (fun N => (interval ω i N 0 ⟨le_rfl, Hp.le⟩).1)
    · exact le_of_tendsto' (zeroLimit ω i) (fun N => (interval ω i N 0 ⟨le_rfl, Hp.le⟩).2)
  have seedBounds (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ) (z : ℝ) (hz : 0 ≤ z ∧ z ≤ H) :
      finitePast ω i N 0 ≤ finitePast ω i N z ∧
      finitePast ω i N z ≤ finitePast ω i N 0 + H * rho ^ N := by
    refine ⟨seedMono ω i N hz.1, ?_⟩
    have delta := difference ω i N 0 z
    have upper := mul_le_mul (contraction ω i N).2 hz.2 hz.1 (pow_nonneg rp.le N)
    simp only [sub_zero] at delta
    nlinarith
  have errorLimit : Tendsto (fun N : ℕ => H * rho ^ N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one rp.le r1).const_mul H
  have seedLimit (ω : ℤ → CuLetter) (i : ℤ) (z : ℝ) (hz : 0 ≤ z ∧ z ≤ H) :
      Tendsto (fun N : ℕ => finitePast ω i N z) atTop (𝓝 (pastState ω i)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (zeroLimit ω i)
      (by simpa using (zeroLimit ω i).add errorLimit)
    · exact fun N => (seedBounds ω i N z hz).1
    · exact fun N => (seedBounds ω i N z hz).2
  have transition (ω : ℤ → CuLetter) (i : ℤ) :
      pastState ω (i + 1) = letterMap (ω i) (pastState ω i) := by
    have shifted : Tendsto (fun N : ℕ => finitePast ω (i + 1) (N + 1) 0) atTop
        (𝓝 (pastState ω (i + 1))) := (tendsto_add_atTop_iff_nat 1).mpr (zeroLimit ω (i + 1))
    have continuous : Continuous (letterMap (ω i)) := by
      cases h : ω i
      · change Continuous (fun z : ℝ => chi * z); fun_prop
      · change Continuous (fun z : ℝ => aSide .high + rho * z); fun_prop
    have mapped := (continuous.tendsto (pastState ω i)).comp (zeroLimit ω i)
    have eqn : (fun N : ℕ => finitePast ω (i + 1) (N + 1) 0) =
        (fun N : ℕ => letterMap (ω i) (finitePast ω i N 0)) := by
      funext N; simp only [finitePast]; congr 2 <;> omega
    rw [eqn] at shifted
    exact tendsto_nhds_unique shifted mapped
  have unroll (ω : ℤ → CuLetter) (y : ℤ → ℝ)
      (hy : ∀ i, y (i + 1) = letterMap (ω i) (y i)) (i : ℤ) (N : ℕ) :
      y i = finitePast ω i N (y (i - (N : ℤ))) := by
    induction N generalizing i with
    | zero => simp [finitePast]
    | succ N ih =>
      have step := hy (i - 1)
      have idx : i - 1 + 1 = i := by omega
      rw [idx, ih (i - 1)] at step
      have idx' : i - 1 - (N : ℤ) = i - ((N + 1 : ℕ) : ℤ) := by push_cast; ring
      simpa only [finitePast, idx'] using step
  have unique (ω : ℤ → CuLetter) (y : ℤ → ℝ)
      (yb : ∀ i, 0 ≤ y i ∧ y i ≤ H)
      (hy : ∀ i, y (i + 1) = letterMap (ω i) (y i)) : y = pastState ω := by
    funext i
    have sandwich (N : ℕ) : finitePast ω i N 0 ≤ y i ∧
        y i ≤ finitePast ω i N 0 + H * rho ^ N := by
      rw [unroll ω y hy i N]
      exact seedBounds ω i N _ (yb _)
    have limit : Tendsto (fun _ : ℕ => y i) atTop (𝓝 (pastState ω i)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le (zeroLimit ω i)
        (by simpa using (zeroLimit ω i).add errorLimit)
        (fun N => (sandwich N).1) (fun N => (sandwich N).2)
    exact tendsto_nhds_unique tendsto_const_nhds limit
  have samePast (ω ν : ℤ → CuLetter) (i : ℤ) (N : ℕ)
      (hn : ∀ k : Fin N, ω (i - 1 - (k : ℕ)) = ν (i - 1 - (k : ℕ))) (z : ℝ) :
      finitePast ω i N z = finitePast ν i N z := by
    induction N generalizing i with
    | zero => rfl
    | succ N ih =>
      have first := hn ⟨0, by omega⟩
      simp only [Nat.cast_zero, sub_zero] at first
      have rest : ∀ k : Fin N, ω (i - 1 - 1 - (k : ℕ)) = ν (i - 1 - 1 - (k : ℕ)) := by
        intro k
        have h := hn ⟨k.val + 1, by omega⟩
        have idx : i - 1 - 1 - (k : ℕ) = i - 1 - ((k.val + 1 : ℕ) : ℤ) := by
          push_cast; ring
        simpa only [idx] using h
      simp only [finitePast, first, ih (i - 1) rest]
  have stability (ω ν : ℤ → CuLetter) (i : ℤ) (N : ℕ)
      (hn : ∀ k : Fin N, ω (i - 1 - (k : ℕ)) = ν (i - 1 - (k : ℕ))) :
      |pastState ω i - pastState ν i| ≤ H * rho ^ N := by
    have bw := seedBounds ω i N _ (stateInterval ω (i - (N : ℤ)))
    have bv := seedBounds ν i N _ (stateInterval ν (i - (N : ℤ)))
    rw [← unroll ω (pastState ω) (transition ω) i N] at bw
    rw [← unroll ν (pastState ν) (transition ν) i N] at bv
    rw [← samePast ω ν i N hn 0] at bv
    exact abs_le.mpr ⟨by linarith [bw.1, bv.2], by linarith [bw.2, bv.1]⟩
  have allU : ∀ i : ℤ, pastState (fun _ => CuLetter.u) i = H := by
    have fixed : (fun _ : ℤ => H) = pastState (fun _ => CuLetter.u) := by
      apply unique
      · intro i; exact ⟨Hp.le, le_rfl⟩
      · intro i; dsimp [letterMap, H, aSide]; ring
    intro i; exact (congrFun fixed i).symm
  have stateContinuous (i : ℤ) : Continuous (fun ω : ℤ → CuLetter => pastState ω i) := by
    apply continuous_iff_continuousAt.mpr
    intro ω
    apply Metric.continuousAt_iff'.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε Hp) r1
    have close : H * rho ^ N < ε := by
      have hn := (lt_div_iff₀ Hp).mp hN
      nlinarith
    have matching : ∀ᶠ ν : ℤ → CuLetter in 𝓝 ω,
        ∀ k : Fin N, ν (i - 1 - (k : ℕ)) = ω (i - 1 - (k : ℕ)) := by
      apply Filter.eventually_all.mpr
      intro k
      have h := (continuous_apply (i - 1 - (k : ℕ))).tendsto ω
      exact h.eventually ((isOpen_discrete {ω (i - 1 - (k : ℕ))}).mem_nhds (by simp))
    filter_upwards [matching] with ν hν
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (stability ν ω i N hν) close
  have runOpen (position : ℕ → ℤ) (n : ℕ) :
      IsOpen {ω : ℤ → CuLetter | ∀ k : Fin n, ω (position k) = .c} := by
    have h := isOpen_iInter_of_finite (fun k : Fin n =>
      (isOpen_discrete ({CuLetter.c} : Set CuLetter)).preimage
        (continuous_apply (position k) : Continuous (fun ω : ℤ → CuLetter => ω (position k))))
    convert h using 1
    ext ω; simp
  have languageClosed (K : ℕ) (d : ℝ) : IsClosed (AuxiliaryLanguage K d) := by
    have noRun (i : ℤ) : IsClosed {ω : ℤ → CuLetter |
        ¬ ∀ k : Fin (K + 1), ω (i + (k : ℕ)) = .c} :=
      (runOpen (fun k => i + (k : ℤ)) (K + 1)).isClosed_compl
    have guard (i : ℤ) : IsClosed {ω : ℤ → CuLetter |
        (∀ k : Fin K, ω (i - (k : ℕ)) = .c) → chi ^ (K - 1) * d ≤ pastState ω i} := by
      have closedBound : IsClosed {ω : ℤ → CuLetter | chi ^ (K - 1) * d ≤ pastState ω i} :=
        isClosed_le (continuous_const : Continuous (fun _ : ℤ → CuLetter => chi ^ (K - 1) * d))
          (stateContinuous i)
      have h := (runOpen (fun k => i - (k : ℤ)) K).isClosed_compl.union
        closedBound
      convert h using 1
      ext ω; simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq]; tauto
    have closed := (isClosed_iInter noRun).inter (isClosed_iInter guard)
    convert closed using 1
    ext ω; simp [AuxiliaryLanguage]
  have stateShift (ω : ℤ → CuLetter) (i j : ℤ) :
      pastState (fun n => ω (n + j)) i = pastState ω (i + j) := by
    have fixed := unique (fun n => ω (n + j)) (fun n => pastState ω (n + j))
      (fun n => stateInterval ω (n + j)) (by
        intro n
        have idx : n + 1 + j = n + j + 1 := by ring
        change pastState ω (n + 1 + j) = letterMap (ω (n + j)) (pastState ω (n + j))
        rw [idx]; exact transition ω (n + j))
    exact (congrFun fixed i).symm
  have shiftForward (ω : ℤ → CuLetter) (j : ℤ) (K : ℕ) (d : ℝ)
      (hω : ω ∈ AuxiliaryLanguage K d) : (fun n => ω (n + j)) ∈ AuxiliaryLanguage K d := by
    constructor
    · intro i hc
      apply hω.1 (i + j)
      intro k
      have hh := hc k
      change ω (i + (k : ℕ) + j) = .c at hh
      have idx : i + j + (k : ℕ) = i + (k : ℕ) + j := by ring
      simpa only [idx] using hh
    · intro i hc
      rw [stateShift]
      apply hω.2 (i + j)
      intro k
      have hh := hc k
      change ω (i - (k : ℕ) + j) = .c at hh
      have idx : i + j - (k : ℕ) = i - (k : ℕ) + j := by ring
      simpa only [idx] using hh
  refine ⟨difference, contraction, stateInterval, ?_, transition, unique, stability,
    allU, stateContinuous, ?_, stateShift, ?_⟩
  · intro ω i z hz0 hzH; exact seedLimit ω i z ⟨hz0, hzH⟩
  · intro K d hK
    constructor
    · refine ⟨fun _ => .u, ?_, ?_⟩
      · intro i hc
        have bad := hc ⟨0, by omega⟩
        cases bad
      · intro i hc
        have bad := hc ⟨0, by omega⟩
        cases bad
    · exact (languageClosed K d).isCompact
  · intro ω j K d
    constructor
    · exact shiftForward ω j K d
    · intro h
      have hh := shiftForward (fun n => ω (n + j)) (-j) K d h
      simpa only [add_assoc, neg_add_cancel, add_zero] using hh


/-- A finite auxiliary word at the origin, with u at every other position. -/
def uPadding (w : List CuLetter) (i : ℤ) : CuLetter :=
  if 0 ≤ i then w[i.toNat]?.getD .u else .u

set_option maxHeartbeats 1000000 in
/-- Weak complete actual lists embed literally in the independent bilateral
language. Padding is auxiliary only; its states strictly dominate the actual
complete-boundary states, and the exact original weight is preserved. -/
theorem auxiliary_lower_padding (K : ℕ) (d : ℝ) (model : Model)
    (xs : List Return) (hK : 1 ≤ K)
    (hw : GuardTrace K d false .high xs (initial .high model)) :
    let ω := uPadding (executionWord xs)
    pastState ω 0 = hSide .high ∧
    (∀ p : ℕ, p ≤ xs.length →
      execute .high (xs.take p) (initial .high model) <
        pastState ω ((executionWord (xs.take p)).length : ℤ)) ∧
    ω ∈ AuxiliaryLanguage K d ∧ Occurs ω (executionWord xs) ∧
    AuxiliaryFactor K d (executionWord xs) ∧
    wordWeight (executionWord xs) = listWeight xs := by
  classical
  rcases bilateral_past_state with
    ⟨_, _, bounds, seedLimit, transition, _, stability, allU, _⟩
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have gp : 0 < g := by dsimp [g, t]; nlinarith
  have cp : 0 < chi := pow_pos gp 20
  have rp : 0 < rho := pow_pos gp 6
  let H := hSide .high
  have Hp : 0 ≤ H := le_trans (bounds (fun _ => .u) 0).1 (bounds (fun _ => .u) 0).2
  have fixed : letterMap .u H = H := by dsimp [letterMap, H, aSide]; ring
  have append (as bs : List Return) : executionWord (as ++ bs) =
      executionWord as ++ executionWord bs := by
    induction as with
    | nil => rfl
    | cons a as ih => simp [executionWord, ih, List.append_assoc]
  have total (w : List CuLetter) (n : ℕ) (hn : n < w.length) :
      uPadding w (n : ℤ) = w[n] := by
    simp [uPadding, List.getElem?_eq_getElem hn]
  have outLeft (w : List CuLetter) (i : ℤ) (hi : i < 0) : uPadding w i = .u := by
    simp [uPadding, not_le.mpr hi]
  have outRight (w : List CuLetter) (i : ℤ) (hi : (w.length : ℤ) ≤ i) :
      uPadding w i = .u := by
    have hn : w.length ≤ i.toNat := by omega
    simp [uPadding, show 0 ≤ i by omega, List.getElem?_eq_none hn]
  let ω := uPadding (executionWord xs)
  have zeroPast (i : ℤ) (hi : i ≤ 0) (N : ℕ) : finitePast ω i N H = H := by
    induction N generalizing i with
    | zero => rfl
    | succ N ih =>
      rw [finitePast, ih (i - 1) (by omega)]
      rw [show ω (i - 1) = .u from outLeft _ _ (by omega)]
      exact fixed
  have stateZero : pastState ω 0 = H := by
    have hlim := seedLimit ω 0 H Hp le_rfl
    have eq : (fun N : ℕ => finitePast ω 0 N H) = fun _ => H := by
      funext N; exact zeroPast 0 le_rfl N
    rw [eq] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  have runC (ν : ℤ → CuLetter) (i : ℤ) (n : ℕ)
      (hc : ∀ k : Fin n, ν (i + (k : ℕ)) = .c) :
      pastState ν (i + (n : ℤ)) = chi ^ n * pastState ν i := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hc0 : ∀ k : Fin n, ν (i + (k : ℕ)) = .c := fun k => hc ⟨k, by omega⟩
      have idx : i + ((n + 1 : ℕ) : ℤ) = (i + (n : ℤ)) + 1 := by omega
      rw [idx, transition, hc ⟨n, by omega⟩]
      change chi * pastState ν (i + (n : ℤ)) = _
      rw [ih hc0, pow_succ]; ring
  have runU (ν : ℤ → CuLetter) (i : ℤ) (n : ℕ)
      (hu : ∀ k : Fin n, ν (i + (k : ℕ)) = .u) :
      pastState ν (i + (n : ℤ)) = H - rho ^ n * (H - pastState ν i) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hu0 : ∀ k : Fin n, ν (i + (k : ℕ)) = .u := fun k => hu ⟨k, by omega⟩
      have idx : i + ((n + 1 : ℕ) : ℤ) = (i + (n : ℤ)) + 1 := by omega
      rw [idx, transition, hu ⟨n, by omega⟩]
      change aSide .high + rho * pastState ν (i + (n : ℤ)) = _
      rw [ih hu0, pow_succ]; dsimp [H, aSide]; ring
  have segment (ν : ℤ → CuLetter) (i : ℤ) (ys : List Return)
      (letters : ∀ k : Fin (executionWord ys).length,
        ν (i + (k : ℕ)) = (executionWord ys)[k]) :
      pastState ν (i + ((executionWord ys).length : ℤ)) =
        execute .high ys (pastState ν i) := by
    induction ys generalizing i with
    | nil => simp [executionWord, execute]
    | cons a ys ih =>
      have len : (executionWord (a :: ys)).length = a.r + a.m + (executionWord ys).length := by
        simp [executionWord]; omega
      have cletters : ∀ k : Fin a.r, ν (i + (k : ℕ)) = .c := by
        intro k
        have hh := letters ⟨k, by rw [len]; omega⟩
        simpa (discharger := omega) [executionWord, List.append_assoc, List.getElem_append, k.isLt] using hh
      have uletters : ∀ k : Fin a.m, ν (i + (a.r : ℤ) + (k : ℕ)) = .u := by
        intro k
        have hh := letters ⟨a.r + k, by rw [len]; omega⟩
        have idx : i + ((a.r + (k : ℕ) : ℕ) : ℤ) = i + (a.r : ℤ) + (k : ℕ) := by omega
        rw [idx] at hh
        simpa (discharger := omega) [executionWord, List.append_assoc, List.getElem_append, k.isLt] using hh
      have after := runU ν (i + a.r) a.m uletters
      rw [runC ν i a.r cletters] at after
      have returnState : pastState ν (i + ((a.r + a.m : ℕ) : ℤ)) =
          returnMap .high a (pastState ν i) := by
        simpa [returnMap, H, add_assoc, Nat.cast_add] using after
      have tailLetters : ∀ k : Fin (executionWord ys).length,
          ν (i + ((a.r + a.m : ℕ) : ℤ) + (k : ℕ)) = (executionWord ys)[k] := by
        intro k
        have hh := letters ⟨a.r + a.m + k, by rw [len]; omega⟩
        have idx : i + ((a.r + a.m + (k : ℕ) : ℕ) : ℤ) =
            i + ((a.r + a.m : ℕ) : ℤ) + (k : ℕ) := by omega
        rw [idx] at hh
        have hr : ¬ a.r + a.m + (k : ℕ) < a.r := by omega
        have hm : ¬ a.r + a.m + (k : ℕ) - a.r < a.m := by omega
        have sub : a.r + a.m + (k : ℕ) - a.r - a.m = (k : ℕ) := by omega
        simpa [executionWord, List.getElem_append, List.append_assoc, hr, hm, sub] using hh
      have hh := ih (i + ((a.r + a.m : ℕ) : ℤ)) tailLetters
      rw [returnState] at hh
      simpa [len, Nat.cast_add, add_assoc, execute] using hh
  have prefixState (pre rest : List Return) (heq : xs = pre ++ rest) :
      pastState ω ((executionWord pre).length : ℤ) = execute .high pre H := by
    have letters : ∀ k : Fin (executionWord pre).length, ω (0 + (k : ℕ)) = (executionWord pre)[k] := by
      intro k
      have e : executionWord xs = executionWord pre ++ executionWord rest := by rw [heq, append]
      have hh := total (executionWord xs) k (by rw [e]; simp; omega)
      simpa [ω, e, List.getElem_append, k.isLt] using hh
    simpa [stateZero] using segment ω 0 pre letters
  have ordered (ys : List Return) (D E : ℝ) (hDE : D < E) :
      execute .high ys D < execute .high ys E := by
    induction ys generalizing D E with
    | nil => exact hDE
    | cons a ys ih =>
      apply ih
      have pos := mul_pos (pow_pos rp a.m) (pow_pos cp a.r)
      have h := mul_pos pos (sub_pos.mpr hDE)
      dsimp [returnMap]; nlinarith
  have initH : initial .high model < H :=
    (actual_complete_boundary_geometry model []).1 .high 0 |>.2
  have coupling (p : ℕ) (hp : p ≤ xs.length) :
      execute .high (xs.take p) (initial .high model) <
        pastState ω ((executionWord (xs.take p)).length : ℤ) := by
    rw [prefixState (xs.take p) (xs.drop p) (List.take_append_drop p xs).symm]
    exact ordered _ _ _ initH
  have traceSplit (pre rest : List Return) (D : ℝ)
      (ht : GuardTrace K d false .high (pre ++ rest) D) :
      GuardTrace K d false .high rest (execute .high pre D) := by
    induction pre generalizing D with
    | nil => exact ht
    | cons a pre ih => exact ih _ ht.2.2
  have locate (ys : List Return) (n : ℕ) (hn : n < (executionWord ys).length)
      (hc : (executionWord ys)[n] = .c) :
      ∃ pre a rest k, ys = pre ++ a :: rest ∧ k < a.r ∧
        n = (executionWord pre).length + k := by
    induction ys generalizing n with
    | nil => simp [executionWord] at hn
    | cons a ys ih =>
      by_cases hr : n < a.r
      · exact ⟨[], a, ys, n, rfl, hr, by simp [executionWord]⟩
      · by_cases hm : n < a.r + a.m
        · have he : (executionWord (a :: ys))[n] = .u := by
            have hsub : n - a.r < a.m := by omega
            simp [executionWord, List.append_assoc, List.getElem_append, hr, hsub]
          rw [he] at hc; cases hc
        · have hn' : n - (a.r + a.m) < (executionWord ys).length := by
            simp only [executionWord, List.length_append, List.length_replicate] at hn; omega
          have hc' : (executionWord ys)[n - (a.r + a.m)] = .c := by
            have hsub : ¬ n - a.r < a.m := by omega
            simpa [executionWord, List.append_assoc, List.getElem_append, hr, hsub,
              Nat.sub_sub] using hc
          obtain ⟨pre, b, rest, k, heq, hk, hidx⟩ := ih _ hn' hc'
          refine ⟨a :: pre, b, rest, k, by simp [heq], hk, ?_⟩
          simp only [executionWord, List.length_append, List.length_replicate]; omega
  have lastU (ys : List Return) (hys : ys ≠ []) :
      (executionWord ys)[(executionWord ys).length - 1]'(by
        cases ys with
        | nil => contradiction
        | cons a rest => simp [executionWord]; have := a.m_pos; omega) = .u := by
    induction ys with
    | nil => contradiction
    | cons a ys ih =>
      by_cases he : ys = []
      · subst ys
        have hm := a.m_pos
        simp (discharger := omega) [executionWord, List.getElem_append]
        omega
      · have hl : 0 < (executionWord ys).length := by
          cases ys with
          | nil => contradiction
          | cons b rest => simp [executionWord]; have := b.m_pos; omega
        simpa (discharger := omega) [executionWord, List.append_assoc, List.getElem_append, hl,
          Nat.add_sub_assoc] using ih he
  have cPosition (i : ℤ) (hc : ω i = .c) :
      ∃ pre a rest k, xs = pre ++ a :: rest ∧ k < a.r ∧
        i = ((executionWord pre).length : ℤ) + (k : ℕ) := by
    have hi : 0 ≤ i := by
      by_contra hh; have hu := outLeft (executionWord xs) i (by omega)
      change ω i = .u at hu; rw [hu] at hc; cases hc
    have hin : i.toNat < (executionWord xs).length := by
      by_contra hh
      have hu := outRight (executionWord xs) i (by omega)
      change ω i = .u at hu; rw [hu] at hc; cases hc
    have hh : (executionWord xs)[i.toNat] = .c := by
      have h : ω i = (executionWord xs)[i.toNat] := by
        simpa [ω, Int.toNat_of_nonneg hi] using total (executionWord xs) i.toNat hin
      exact h.symm.trans hc
    obtain ⟨pre, a, rest, k, heq, hk, hidx⟩ := locate xs i.toNat hin hh
    exact ⟨pre, a, rest, k, heq, hk, by omega⟩
  have runData (pre : List Return) (a : Return) (rest : List Return)
      (heq : xs = pre ++ a :: rest) :
      (∀ k : Fin a.r, ω ((executionWord pre).length + (k : ℕ)) = .c) ∧
      ω ((executionWord pre).length + (a.r : ℤ)) = .u ∧
      ω (((executionWord pre).length : ℤ) - 1) = .u := by
    have e : executionWord xs = executionWord pre ++
        (List.replicate a.r .c ++ List.replicate a.m .u ++ executionWord rest) := by
      rw [heq, append, executionWord]
    have len : (executionWord xs).length =
        (executionWord pre).length + a.r + a.m + (executionWord rest).length := by simp [e]; omega
    refine ⟨?_, ?_, ?_⟩
    · intro k
      have h := total (executionWord xs) ((executionWord pre).length + k) (by rw [len]; omega)
      simpa (discharger := omega) [ω, e, List.getElem_append, List.append_assoc, k.isLt] using h
    · have h := total (executionWord xs) ((executionWord pre).length + a.r) (by
        rw [len]; have := a.m_pos; omega)
      simpa (discharger := omega) [ω, e, List.getElem_append, List.append_assoc, a.m_pos] using h
    · by_cases hp : pre = []
      · subst pre; simpa [executionWord] using outLeft (executionWord xs) (-1) (by omega)
      · have hl : 0 < (executionWord pre).length := by
          cases pre with
          | nil => contradiction
          | cons b ys => simp [executionWord]; have := b.m_pos; omega
        have h := total (executionWord xs) ((executionWord pre).length - 1) (by rw [len]; omega)
        have idx : (((executionWord pre).length - 1 : ℕ) : ℤ) =
            ((executionWord pre).length : ℤ) - 1 := by omega
        rw [idx] at h
        simpa (discharger := omega) [ω, e, List.getElem_append, lastU pre hp] using h
  have language : ω ∈ AuxiliaryLanguage K d := by
    constructor
    · intro i hc
      obtain ⟨pre, a, rest, k, heq, hk, hidx⟩ := cPosition i (by simpa using hc ⟨0, by omega⟩)
      have ht := traceSplit pre (a :: rest) _ (by simpa [heq] using hw)
      have hcap := ht.1
      have hu := (runData pre a rest heq).2.1
      have hbad := hc ⟨a.r - k, by omega⟩
      have idx : i + ((a.r - k : ℕ) : ℤ) =
          ((executionWord pre).length : ℤ) + a.r := by omega
      rw [idx, hu] at hbad; cases hbad
    · intro i hc
      obtain ⟨pre, a, rest, k, heq, hk, hidx⟩ := cPosition i (by simpa using hc ⟨0, by omega⟩)
      have ht := traceSplit pre (a :: rest) _ (by simpa [heq] using hw)
      have hcap := ht.1
      have rd := runData pre a rest heq
      have hback : K - 1 ≤ k := by
        by_contra hh
        have hbad := hc ⟨k + 1, by omega⟩
        have idx : i - ((k + 1 : ℕ) : ℤ) = ((executionWord pre).length : ℤ) - 1 := by omega
        rw [idx, rd.2.2] at hbad; cases hbad
      have kr : k = K - 1 ∧ a.r = K := by omega
      have guard := ht.2.1 kr.2
      simp only [Bool.false_eq_true, if_false] at guard
      have value := runC ω ((executionWord pre).length : ℤ) k
        (fun j => rd.1 ⟨j, by omega⟩)
      rw [← hidx] at value
      rw [value, kr.1]
      apply mul_le_mul_of_nonneg_left _ (pow_pos cp (K - 1)).le
      have st := prefixState pre (a :: rest) heq
      rw [st]
      exact guard.trans (ordered pre _ _ initH).le
  have occurrence : Occurs ω (executionWord xs) := by
    refine ⟨0, ?_⟩; intro k; simpa using total (executionWord xs) k k.isLt
  exact ⟨stateZero, coupling, language, occurrence, ⟨ω, language, occurrence⟩,
    complete_execution_word_parser.2.2.2.1 xs⟩


set_option maxHeartbeats 1000000 in
/-- Any finite binary word ending in u has a unique leading u run followed by
positive complete c/u returns. The first and last runs may be truncated. -/
theorem finite_run_decomposition (w : List CuLetter)
    (hend : w = [] ∨ w.getLast? = some CuLetter.u) :
    ∃! p : ℕ × List Return,
      w = List.replicate p.1 CuLetter.u ++ executionWord p.2 := by
  have existence (v : List CuLetter) (hv : v = [] ∨ v.getLast? = some CuLetter.u) :
      ∃ a : ℕ, ∃ xs : List Return,
        v = List.replicate a CuLetter.u ++ executionWord xs := by
    induction v with
    | nil => exact ⟨0, [], rfl⟩
    | cons l v ih =>
      cases v with
      | nil =>
        cases l
        · simp at hv
        · exact ⟨1, [], rfl⟩
      | cons y v =>
        have ht : (y :: v).getLast? = some CuLetter.u := by
          simpa using hv
        obtain ⟨a, xs, heq⟩ := ih (Or.inr ht)
        cases l
        · cases a with
          | zero =>
            cases xs with
            | nil => simp [executionWord] at heq
            | cons b xs =>
              let b' : Return := ⟨b.m, b.r + 1, b.m_pos, by omega⟩
              refine ⟨0, b' :: xs, ?_⟩
              simp only [List.replicate_zero, List.nil_append] at heq ⊢
              rw [heq]
              simp [executionWord, b', List.replicate_succ]
          | succ a =>
            let b : Return := ⟨a + 1, 1, by omega, by decide⟩
            refine ⟨0, b :: xs, ?_⟩
            rw [heq]
            simp [executionWord, b]
        · refine ⟨a + 1, xs, ?_⟩
          rw [heq]
          simp [List.replicate_succ]
  have first (a : ℕ) (xs : List Return) :
      (List.replicate a CuLetter.u ++ executionWord xs).takeWhile isU =
        List.replicate a CuLetter.u := by
    have hxs : (executionWord xs).takeWhile isU = [] := by
      cases xs with
      | nil => rfl
      | cons b xs =>
        obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt b.r_pos)
        simp [executionWord, hr, List.replicate_succ, isU]
    induction a with
    | zero => simpa using hxs
    | succ a ih => simp [List.replicate_succ, List.takeWhile_cons, isU, ih]
  obtain ⟨a, xs, h⟩ := existence w hend
  refine ⟨(a, xs), h, ?_⟩
  rintro ⟨b, ys⟩ hy
  have ha : b = a := by
    have hh := congrArg (fun v : List CuLetter => (v.takeWhile isU).length) (hy.symm.trans h)
    simpa only [first, List.length_replicate] using hh
  have hxs : ys = xs := by
    apply complete_execution_word_parser.2.2.1
    rw [ha] at hy
    exact List.append_cancel_left (hy.symm.trans h)
  simp only [Prod.mk.injEq]
  exact ⟨ha, hxs⟩


set_option maxHeartbeats 1000000 in
/-- An independently occurring complete word, with only its final u allowed to
be a terminal fill, inherits the exact cap and before-Kth-c return guards. -/
theorem occurrence_run_guards (K : ℕ) (d : ℝ) (hK : 1 ≤ K)
    (ω : ℤ → CuLetter) (hω : ω ∈ AuxiliaryLanguage K d)
    (i : ℤ) (xs : List Return)
    (letters : ∀ k : Fin (executionWord xs).length,
      (k.val + 1 < (executionWord xs).length ∨ (executionWord xs)[k.val] = .c) →
      ω (i + (k : ℕ)) = (executionWord xs)[k.val]) :
    GuardTrace K d false .high xs (pastState ω i) := by
  rcases bilateral_past_state with ⟨_, _, _, _, transition, _⟩
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have gp : 0 < g := by dsimp [g, t]; nlinarith
  have cp : 0 < chi := pow_pos gp 20
  have runC (j : ℤ) (n : ℕ)
      (hc : ∀ k : Fin n, ω (j + (k : ℕ)) = .c) :
      pastState ω (j + (n : ℤ)) = chi ^ n * pastState ω j := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hc0 : ∀ k : Fin n, ω (j + (k : ℕ)) = .c := fun k => hc ⟨k, by omega⟩
      have idx : j + ((n + 1 : ℕ) : ℤ) = (j + (n : ℤ)) + 1 := by omega
      rw [idx, transition, hc ⟨n, by omega⟩]
      change chi * pastState ω (j + (n : ℤ)) = _
      rw [ih hc0, pow_succ]; ring
  have runU (j : ℤ) (n : ℕ)
      (hu : ∀ k : Fin n, ω (j + (k : ℕ)) = .u) :
      pastState ω (j + (n : ℤ)) = hSide .high -
        rho ^ n * (hSide .high - pastState ω j) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hu0 : ∀ k : Fin n, ω (j + (k : ℕ)) = .u := fun k => hu ⟨k, by omega⟩
      have idx : j + ((n + 1 : ℕ) : ℤ) = (j + (n : ℤ)) + 1 := by omega
      rw [idx, transition, hu ⟨n, by omega⟩]
      change aSide .high + rho * pastState ω (j + (n : ℤ)) = _
      rw [ih hu0, pow_succ]; dsimp [aSide]; ring
  induction xs generalizing i with
  | nil => trivial
  | cons a xs ih =>
    have len : (executionWord (a :: xs)).length = a.r + a.m + (executionWord xs).length := by
      simp [executionWord]; omega
    have cletters : ∀ k : Fin a.r, ω (i + (k : ℕ)) = .c := by
      intro k
      have atC : (executionWord (a :: xs))[k.val]'(by omega) = .c := by
        simp (discharger := omega) [executionWord, List.append_assoc, List.getElem_append, k.isLt]
      have hh := letters ⟨k, by omega⟩ (Or.inr atC)
      exact hh.trans atC
    have cap : a.r ≤ K := by
      by_contra hn
      exact hω.1 i (fun k => cletters ⟨k, by omega⟩)
    have guard : a.r = K → d ≤ pastState ω i := by
      intro hr
      have atGuard : ∀ k : Fin K, ω (i + ((K - 1 : ℕ) : ℤ) - (k : ℕ)) = .c := by
        intro k
        have idx : i + ((K - 1 : ℕ) : ℤ) - (k : ℕ) =
            i + ((K - 1 - k.val : ℕ) : ℤ) := by omega
        rw [idx]; exact cletters ⟨K - 1 - k.val, by omega⟩
      have hg := hω.2 (i + ((K - 1 : ℕ) : ℤ)) atGuard
      have hc : ∀ k : Fin (K - 1), ω (i + (k : ℕ)) = .c :=
        fun k => cletters ⟨k, by omega⟩
      rw [runC i (K - 1) hc] at hg
      exact (mul_le_mul_iff_right₀ (pow_pos cp (K - 1))).mp hg
    refine ⟨cap, guard, ?_⟩
    cases xs with
    | nil => trivial
    | cons b xs =>
      have tailLen : 0 < (executionWord (b :: xs)).length := by
        simp [executionWord]; have hb := b.r_pos; omega
      have uletters : ∀ k : Fin a.m, ω (i + (a.r : ℤ) + (k : ℕ)) = .u := by
        intro k
        have hh := letters ⟨a.r + k, by omega⟩ (Or.inl (by change a.r + k.val + 1 < _; omega))
        have idx : i + ((a.r + k.val : ℕ) : ℤ) = i + (a.r : ℤ) + (k : ℕ) := by omega
        rw [idx] at hh
        simpa (discharger := omega) [executionWord, List.append_assoc, List.getElem_append, k.isLt] using hh
      have after := runU (i + a.r) a.m uletters
      rw [runC i a.r cletters] at after
      have returnState : pastState ω (i + ((a.r + a.m : ℕ) : ℤ)) =
          returnMap .high a (pastState ω i) := by
        simpa [returnMap, add_assoc, Nat.cast_add] using after
      have tailLetters : ∀ k : Fin (executionWord (b :: xs)).length,
          (k.val + 1 < (executionWord (b :: xs)).length ∨ (executionWord (b :: xs))[k.val] = .c) →
          ω (i + ((a.r + a.m : ℕ) : ℤ) + (k : ℕ)) = (executionWord (b :: xs))[k.val] := by
        intro k hk
        have atTail : (executionWord (a :: b :: xs))[a.r + a.m + k.val]'(by omega) =
            (executionWord (b :: xs))[k.val] := by
          have hr : ¬ a.r + a.m + k.val < a.r := by omega
          have hm : ¬ a.r + a.m + k.val - a.r < a.m := by omega
          have sub : a.r + a.m + k.val - a.r - a.m = k.val := by omega
          simp [executionWord, List.getElem_append, List.append_assoc, hr, hm, sub]
        have hh := letters ⟨a.r + a.m + k, by omega⟩ (by
          rcases hk with hk | hk
          · exact Or.inl (by change a.r + a.m + k.val + 1 < _; omega)
          · exact Or.inr (atTail.trans hk))
        have idx : i + ((a.r + a.m + k.val : ℕ) : ℤ) =
            i + ((a.r + a.m : ℕ) : ℤ) + (k : ℕ) := by omega
        simp only [Fin.val_mk] at hh
        rw [idx, atTail] at hh
        exact hh
      have hh := ih (i + ((a.r + a.m : ℕ) : ℤ)) tailLetters
      rwa [returnState] at hh


set_option maxHeartbeats 1500000 in
/-- Every genuine c-containing factor has a canonically parsed strict actual
completion from either original start, with the prescribed first-run insertion
and the exact ending-class weight overhead. -/
theorem auxiliary_factor_upper_completion (o : Ownership) (b : ℝ) (K : ℕ)
    (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K))) :
    ∃ R : Return, R.r = 1 ∧
      ∀ (model : Model) (w : List CuLetter),
        AuxiliaryFactor K ((lam - b) / g ^ 2 / chi ^ K) w → CuLetter.c ∈ w →
        ∃ (a : ℕ) (first : Return) (rest : List Return),
          let filled := if w.getLast? = some CuLetter.c then w ++ [CuLetter.u] else w
          let reset : Return := ⟨R.m + a, 1, by have := R.m_pos; omega, by decide⟩
          let extra : Return := ⟨first.m + 1, first.r, by omega, first.r_pos⟩
          filled = List.replicate a CuLetter.u ++ executionWord (first :: rest) ∧
          (∀ (a' : ℕ) (xs' : List Return),
            filled = List.replicate a' CuLetter.u ++ executionWord xs' →
            a' = a ∧ xs' = first :: rest) ∧
          ActualPairSupply model o b .strict (reset :: extra :: rest) ∧
          executionWord (reset :: extra :: rest) =
            CuLetter.c :: (List.replicate (R.m + a) CuLetter.u ++
              List.replicate first.r CuLetter.c ++
              List.replicate (first.m + 1) CuLetter.u ++ executionWord rest) ∧
          listWeight (reset :: extra :: rest) = wordWeight w + (20 + 6 * R.m) +
            (if w.getLast? = some CuLetter.c then 12 else 6) := by
  classical
  let d := (lam - b) / g ^ 2 / chi ^ K
  rcases actual_reset_first_return o b K hK hqb hbp with
    ⟨R, hr, hB, hStrict, hWeak, hTransfer, hWeight, hIncrease⟩
  refine ⟨R, hr, ?_⟩
  intro model w hw hc
  rcases hw with ⟨ω, hω, i, occurrence⟩
  let filled := if w.getLast? = some CuLetter.c then w ++ [CuLetter.u] else w
  have endCases (v : List CuLetter) (hv : v ≠ []) :
      v.getLast? = some CuLetter.c ∨ v.getLast? = some CuLetter.u := by
    induction v with
    | nil => contradiction
    | cons l v ih =>
      cases v with
      | nil => cases l <;> simp
      | cons y v => simpa using ih (by simp)
  have wne : w ≠ [] := by intro hn; simp [hn] at hc
  have filledEnd : filled.getLast? = some CuLetter.u := by
    rcases endCases w wne with he | he
    · simp [filled, he]
    · simp [filled, he]
  rcases finite_run_decomposition filled (Or.inr filledEnd) with ⟨⟨a, xs⟩, parse, unique⟩
  have cf : CuLetter.c ∈ filled := by dsimp [filled]; split <;> simp_all
  cases xs with
  | nil =>
    rw [parse] at cf
    simp [executionWord] at cf
  | cons first rest =>
    let reset : Return := ⟨R.m + a, 1, by have := R.m_pos; omega, by decide⟩
    let extra : Return := ⟨first.m + 1, first.r, by omega, first.r_pos⟩
    have plen : filled.length = a + (executionWord (first :: rest)).length := by
      rw [parse]; simp
    have originalLetter (n : ℕ) (hn : n < filled.length)
        (hnc : n + 1 < filled.length ∨ filled[n] = .c) :
        ∃ hnw : n < w.length, filled[n] = w[n] := by
      by_cases he : w.getLast? = some CuLetter.c
      · have feq : filled = w ++ [CuLetter.u] := by simp [filled, he]
        have flen : filled.length = w.length + 1 := by simp [feq]
        by_cases hnw : n < w.length
        · refine ⟨hnw, ?_⟩; simp [feq, List.getElem_append, hnw]
        · have neq : n = w.length := by omega
          have fu : filled[n] = .u := by simp [feq, List.getElem_append, hnw, neq]
          rcases hnc with hnc | hnc
          · omega
          · rw [fu] at hnc; cases hnc
      · have feq : filled = w := by simp [filled, he]
        refine ⟨by simpa [feq] using hn, ?_⟩
        simp [feq]
    have letters : ∀ k : Fin (executionWord (first :: rest)).length,
        (k.val + 1 < (executionWord (first :: rest)).length ∨
          (executionWord (first :: rest))[k.val] = .c) →
        ω (i + (a : ℤ) + (k : ℕ)) = (executionWord (first :: rest))[k.val] := by
      intro k hk
      have atParsed : filled[a + k.val]'(by omega) = (executionWord (first :: rest))[k.val] := by
        simp [parse, List.getElem_append, show ¬ a + k.val < a by omega,
          show a + k.val - a = k.val by omega]
      have hcond : a + k.val + 1 < filled.length ∨ filled[a + k.val] = .c := by
        rcases hk with hk | hk
        · exact Or.inl (by omega)
        · exact Or.inr (atParsed.trans hk)
      obtain ⟨hnw, heq⟩ := originalLetter (a + k.val) (by omega) hcond
      have hh := occurrence ⟨a + k.val, hnw⟩
      have idx : i + ((a + k.val : ℕ) : ℤ) = i + (a : ℤ) + (k : ℕ) := by omega
      simpa only [idx] using hh.trans (heq.symm.trans atParsed)
    have trace := occurrence_run_guards K d (by omega) ω hω (i + a) (first :: rest) letters
    rcases bilateral_past_state with ⟨_, _, bounds, _⟩
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    have hs0 := Real.sqrt_nonneg (5 : ℝ)
    have gp : 0 < g := by dsimp [g, t]; nlinarith
    have g1 : g < 1 := by dsimp [g, t]; nlinarith
    have cp : 0 < chi := pow_pos gp 20
    have rp : 0 < rho := pow_pos gp 6
    have c1 : chi < 1 := pow_lt_one₀ gp.le g1 (by decide)
    have r1 : rho < 1 := pow_lt_one₀ gp.le g1 (by decide)
    have hp : 0 < hSide .high := by dsimp [hSide]; nlinarith
    have ap : 0 < aSide .high := mul_pos (sub_pos.mpr r1) hp
    have initialBounds := (actual_complete_boundary_geometry model []).1 .high 0
    simp only [List.take_nil, execute] at initialBounds
    have initialPos : 0 < initial .high model := lt_trans ap initialBounds.1
    have gap : 0 ≤ hSide .high - chi * initial .high model := by
      have hh := mul_le_mul_of_nonneg_right c1.le initialPos.le
      linarith [initialBounds.2]
    have pm : rho ^ (R.m + a) ≤ rho ^ R.m :=
      pow_le_pow_of_le_one rp.le r1.le (by omega)
    have merged : returnMap .high R (initial .high model) ≤
        returnMap .high reset (initial .high model) := by
      have hh := mul_le_mul_of_nonneg_right pm gap
      dsimp [returnMap, reset]; rw [hr]; simp only [pow_one]; linarith
    let z := returnMap .high reset (initial .high model)
    have bz : hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) < z :=
      lt_of_lt_of_le (hStrict _ initialBounds.1) merged
    have dz : d < z := by
      have dd := lt_of_le_of_lt (le_max_right
        (max (xSide .high) (ySide .high)) d) hB
      exact lt_trans dd bz
    have za : aSide .high ≤ z := by
      have hh := (actual_complete_boundary_geometry model [reset]).1 .high 1
      simpa [execute, z] using hh.1.le
    have ordered (a0 : Return) (D E : ℝ) (hDE : D < E) :
        returnMap .high a0 D < returnMap .high a0 E := by
      have hh := mul_pos (mul_pos (pow_pos rp a0.m) (pow_pos cp a0.r)) (sub_pos.mpr hDE)
      dsimp [returnMap]; nlinarith
    have improve (ys : List Return) (D E : ℝ) (hDE : D < E)
        (hh : GuardTrace K d false .high ys D) : GuardTrace K d true .high ys E := by
      induction ys generalizing D E with
      | nil => trivial
      | cons a0 ys ih =>
        refine ⟨hh.1, ?_, ih _ _ (ordered a0 D E hDE) hh.2.2⟩
        intro heq
        have hg := hh.2.1 heq
        simp only [Bool.false_eq_true, if_false] at hg
        simp only [if_true]; linarith
    have firstOutput : returnMap .high first (pastState ω (i + a)) <
        returnMap .high extra z := by
      have hi := (hIncrease first.m first.r z (by have := first.m_pos; omega)
        (by have := first.r_pos; omega) trace.1 za).2
      have weak : returnMap .high first (pastState ω (i + a)) ≤
          returnMap .high first (hSide .high) := by
        have hh := mul_nonneg (mul_pos (pow_pos rp first.m) (pow_pos cp first.r)).le
          (sub_nonneg.mpr (bounds ω (i + a)).2)
        dsimp [returnMap]; nlinarith
      have strong : returnMap .high first (hSide .high) < returnMap .high extra z := by
        dsimp [returnMap, extra] at *; linarith only [hi]
      exact lt_of_le_of_lt weak strong
    have actualTrace : GuardTrace K d true .high (reset :: extra :: rest) (initial .high model) := by
      refine ⟨by dsimp [reset]; omega, ?_, ?_⟩
      · intro heq; dsimp [reset] at heq; omega
      · refine ⟨trace.1, ?_, improve rest _ _ firstOutput trace.2.2⟩
        intro heq; exact dz
    have actual := (actual_strict_record_supply model o b (reset :: extra :: rest)
      K hK hqb hbp).1.mpr actualTrace
    have appendWeight (v v' : List CuLetter) : wordWeight (v ++ v') = wordWeight v + wordWeight v' := by
      induction v with
      | nil => simp [wordWeight]
      | cons l v ih => cases l <;> simp [wordWeight, ih, Nat.add_assoc]
    have uWeight (n : ℕ) : wordWeight (List.replicate n CuLetter.u) = 6 * n := by
      induction n with
      | zero => rfl
      | succ n ih => simp [List.replicate_succ, wordWeight, ih]; omega
    have parsedWeight : wordWeight filled = 6 * a + listWeight (first :: rest) := by
      rw [parse, appendWeight, uWeight, complete_execution_word_parser.2.2.2.1]
    refine ⟨a, first, rest, parse, ?_, actual, ?_, ?_⟩
    · intro a' xs' hparse
      have hh := unique (a', xs') hparse
      exact Prod.mk.inj hh
    · simp [executionWord, reset, extra, List.append_assoc]
    · have fw : wordWeight filled = wordWeight w +
          (if w.getLast? = some CuLetter.c then 6 else 0) := by
        dsimp [filled]; split <;> simp [appendWeight, wordWeight]
      dsimp [reset, extra, listWeight] at *
      split <;> simp_all <;> omega

/-- At a fixed original variable weight, the actual eventually-empty address on
 either side determines the execution list. The fixed stem and paid anchor are
 removed from equal-length observed prefixes, without reversing block letters. -/
theorem actual_source_address_injection (j : Side) (model : Model)
    (xs ys : List Return) (hweight : listWeight xs = listWeight ys)
    (hsource : source j model xs = source j model ys) : xs = ys := by
  let encode (w : List CuLetter) : List Label :=
    (w.map (fun l => match l with | .c => C | .u => block j)).flatten
  have encodeAppend (w v : List CuLetter) : encode (w ++ v) = encode w ++ encode v := by
    simp [encode, List.map_append, List.flatten_append]
  have encodeRepC (n : ℕ) : encode (List.replicate n CuLetter.c) = repeatWord C n := by
    induction n with
    | zero => simp [encode, repeatWord]
    | succ n ih =>
      rw [List.replicate_succ]
      change _ ++ encode _ = _ ++ _
      rw [ih]
  have encodeRepU (n : ℕ) : encode (List.replicate n CuLetter.u) = repeatWord (block j) n := by
    induction n with
    | zero => simp [encode, repeatWord]
    | succ n ih =>
      rw [List.replicate_succ]
      change _ ++ encode _ = _ ++ _
      rw [ih]
  have encodeInj : Function.Injective encode := by
    intro w
    induction w with
    | nil =>
      intro v heq
      cases v with
      | nil => rfl
      | cons l v => cases l <;> cases j <;> simp [encode, block, U, V, C] at heq
    | cons l w ih =>
      intro v heq
      cases v with
      | nil => cases l <;> cases j <;> simp [encode, block, U, V, C] at heq
      | cons k v =>
        cases l <;> cases k
        · have h : encode w = encode v := by
            exact List.append_cancel_left
              (by simpa only [encode, List.map_cons, List.flatten_cons] using heq)
          exact congrArg (List.cons CuLetter.c) (ih h)
        · cases j
          · have h := congrArg (fun x : List Label => x[1]?) heq
            simp [encode, block, U, C] at h
          · have h := congrArg (fun x : List Label => x[0]?) heq
            simp [encode, block, V, C] at h
        · cases j
          · have h := congrArg (fun x : List Label => x[1]?) heq
            simp [encode, block, U, C] at h
          · have h := congrArg (fun x : List Label => x[0]?) heq
            simp [encode, block, V, C] at h
        · have h : encode w = encode v := by
            exact List.append_cancel_left
              (by simpa only [encode, List.map_cons, List.flatten_cons] using heq)
          exact congrArg (List.cons CuLetter.u) (ih h)
  have encoded (zs : List Return) : encode (executionWord zs).reverse = externalWord j zs := by
    induction zs with
    | nil => simp [encode, executionWord, externalWord]
    | cons a zs ih =>
      simp [executionWord, List.reverse_append, List.reverse_replicate, encodeAppend,
        encodeRepC, encodeRepU, ih, externalWord, List.reverse_cons, returnWord,
        List.map_append, List.flatten_append, List.append_assoc]
  have plen : (observedPrefix j model xs).length = (observedPrefix j model ys).length := by
    rw [(paired_source_reconstruction j model xs).2.2.2.2.1,
      (paired_source_reconstruction j model ys).2.2.2.2.1, hweight]
  have hpref : observedPrefix j model xs = observedPrefix j model ys := by
    apply List.ext_getElem plen
    intro p hp hq
    have h := congrFun hsource p
    simpa only [source, address, sourcePrefix, List.getElem?_append_left hp,
      List.getElem?_append_left hq, List.getElem?_eq_getElem hp,
      List.getElem?_eq_getElem hq, Option.getD_some] using h
  have ext : externalWord j xs = externalWord j ys := by
    unfold observedPrefix at hpref
    exact List.append_cancel_left (List.append_cancel_right hpref)
  have enc : encode (executionWord xs).reverse = encode (executionWord ys).reverse := by
    rw [encoded, encoded]; exact ext
  apply complete_execution_word_parser.2.2.1
  have h := encodeInj enc
  simpa only [List.reverse_reverse] using congrArg List.reverse h


set_option maxHeartbeats 4000000 in
-- Actual record construction and finite liveness share the full decoder recurrence.
/-- Complete readable configurations evolve without reading the append-only output.
Safety and positionwise liveness on actual records separate the original paired
family at the unobserved-terminal departure cut. The actual first stem difference
is zero, so the joint prefix factor is one and configuration separation follows. -/
theorem actual_decoder_configuration_extraction
    {Configuration : Type*}
    (advance : Configuration → Color → Configuration × List Label)
    (initialConfiguration : Configuration) (initialOutput : List Label)
    (model : Model) (o : Ownership) (b : ℝ) (contract : Contract)
    (N : ℕ) (family : Finset (List Return))
    (weight : ∀ xs ∈ family, listWeight xs = N)
    (supply : ∀ xs ∈ family, ActualPairSupply model o b contract xs) :
    let evolve := fun (v : Configuration × List Label) (c : Color) =>
      let next := advance v.1 c
      (next.1, v.2 ++ next.2)
    let run := fun h : List Color => h.foldl evolve (initialConfiguration, initialOutput)
    let front := fun (r : ℕ → Color) (n : ℕ) => List.ofFn (fun p : Fin n => r p.val)
    let omega := fun (a : ℕ → Label) (x : ℕ → ℝ) =>
      ∃ path : ℕ → Guard, path 0 = .G0 ∧
        (∀ p, nextGuard (path p) (a p) = some (path (p + 1))) ∧
        (∀ p, InSupport (path p) (x p)) ∧
        (∀ p, x p = branch (a p) (x (p + 1)))
    let record := fun (a : ℕ → Label) (r : ℕ → Color) =>
      ∃ x : ℕ → ℝ, omega a x ∧ ∃ err : ℕ → ℝ,
        ErrorBound b contract err ∧ ∀ p, observe o (x p) (err p) = r p
    let finiteSource := fun a : ℕ → Label => ∃ M : ℕ, ∀ p, M ≤ p → a p = .L0
    let pairedRecord := fun (xs : List Return) (j : Side) (p : ℕ) =>
      if hp : p < (history model xs).length then (history model xs)[p]
      else observe o (coordinate (tailPrefix j) (p - (history model xs).length)) 0
    (∀ a r, record a r → ∀ n p (hp : p < (run (front r n)).2.length),
      (run (front r n)).2[p] = a p) →
    (∀ a r, record a r → finiteSource a → ∀ p, ∃ n, p < (run (front r n)).2.length) →
    letI := Classical.decEq Configuration
    (∀ xs ∈ family, ∀ j,
      record (source j model xs) (pairedRecord xs j) ∧ finiteSource (source j model xs)) ∧
    (∀ xs ∈ family, (run (history model xs)).2 = []) ∧
    Set.InjOn (fun xs => run (history model xs)) (family : Set (List Return)) ∧
    Set.InjOn (fun xs => (run (history model xs)).1) (family : Set (List Return)) ∧
    family.card ≤ (family.image (fun xs => (run (history model xs)).1)).card * (0 + 1) := by
  classical
  dsimp only
  let evolve := fun (v : Configuration × List Label) (c : Color) =>
    let next := advance v.1 c
    (next.1, v.2 ++ next.2)
  let run := fun h : List Color => h.foldl evolve (initialConfiguration, initialOutput)
  let front := fun (r : ℕ → Color) (n : ℕ) => List.ofFn (fun p : Fin n => r p.val)
  let omega := fun (a : ℕ → Label) (x : ℕ → ℝ) =>
    ∃ path : ℕ → Guard, path 0 = .G0 ∧
      (∀ p, nextGuard (path p) (a p) = some (path (p + 1))) ∧
      (∀ p, InSupport (path p) (x p)) ∧
      (∀ p, x p = branch (a p) (x (p + 1)))
  let record := fun (a : ℕ → Label) (r : ℕ → Color) =>
    ∃ x : ℕ → ℝ, omega a x ∧ ∃ err : ℕ → ℝ,
      ErrorBound b contract err ∧ ∀ p, observe o (x p) (err p) = r p
  let finiteSource := fun a : ℕ → Label => ∃ M : ℕ, ∀ p, M ≤ p → a p = .L0
  let pairedRecord := fun (xs : List Return) (j : Side) (p : ℕ) =>
    if hp : p < (history model xs).length then (history model xs)[p]
    else observe o (coordinate (tailPrefix j) (p - (history model xs).length)) 0
  change (∀ a r, record a r → ∀ n p (hp : p < (run (front r n)).2.length),
    (run (front r n)).2[p] = a p) →
    (∀ a r, record a r → finiteSource a → ∀ p, ∃ n, p < (run (front r n)).2.length) → _
  intro safety liveness
  have actual (xs : List Return) (hx : xs ∈ family) (j : Side) :
      record (source j model xs) (pairedRecord xs j) ∧ finiteSource (source j model xs) := by
    have reconstruction := paired_source_reconstruction j model xs
    obtain ⟨path, hzero, hedges, hsupport, haffine⟩ :=
      literal_address_path .G0 .G0 (sourcePrefix j model xs) reconstruction.1
    obtain ⟨err, hbound, hslots, hzeroErr, hfuture⟩ := supply xs hx j
    have lengths : (observedPrefix j model xs).length = (history model xs).length :=
      reconstruction.2.2.2.2.1.trans reconstruction.2.2.2.2.2.1.symm
    constructor
    · refine ⟨coordinate (sourcePrefix j model xs), ⟨path, hzero, hedges, hsupport, haffine⟩,
        err, hbound, ?_⟩
      intro p
      by_cases hp : p < (history model xs).length
      · simpa only [pairedRecord, dif_pos hp] using hslots p hp
      · have hge : (history model xs).length ≤ p := Nat.le_of_not_gt hp
        have he : (observedPrefix j model xs).length + (p - (history model xs).length) = p := by
          rw [lengths, Nat.add_sub_of_le hge]
        have hf := hfuture (p - (history model xs).length)
        rw [he] at hf
        simpa only [pairedRecord, dif_neg hp] using hf
    · refine ⟨(sourcePrefix j model xs).length, ?_⟩
      intro p hp
      simp only [source, address, List.getElem?_eq_none hp, Option.getD_none]
  have past (xs : List Return) (j : Side) :
      front (pairedRecord xs j) (history model xs).length = history model xs := by
    apply List.ext_getElem (by simp [front])
    intro p hp hq
    simp [front, pairedRecord, hq]
  have frontAdd (r : ℕ → Color) (n m : ℕ) :
      front r (n + m) = front r n ++ front (fun p => r (n + p)) m := by
    simp [front, List.ofFn_add]
  have splice (xs : List Return) (j : Side) (n : ℕ) :
      front (pairedRecord xs j) ((history model xs).length + n) =
        history model xs ++ front (fun p => observe o (coordinate (tailPrefix j) p) 0) n := by
    rw [frontAdd, past]
    have same : (fun p => pairedRecord xs j ((history model xs).length + p)) =
        (fun p => observe o (coordinate (tailPrefix j) p) 0) := by
      funext p
      have hn : ¬ (history model xs).length + p < (history model xs).length := by omega
      simp only [pairedRecord, dif_neg hn, Nat.add_sub_cancel_left]
    exact congrArg (fun r : ℕ → Color => history model xs ++ front r n) same
  have emittedEmpty (xs : List Return) (hx : xs ∈ family) :
      (run (history model xs)).2 = [] := by
    have hh := (actual xs hx .high).1
    have hl := (actual xs hx .low).1
    cases ho : (run (history model xs)).2 with
    | nil => rfl
    | cons l rest =>
      have hhpos : 0 < (run (front (pairedRecord xs .high) (history model xs).length)).2.length := by
        rw [past, ho]; simp
      have hlpos : 0 < (run (front (pairedRecord xs .low) (history model xs).length)).2.length := by
        rw [past, ho]; simp
      have hhigh := safety _ _ hh (history model xs).length 0 hhpos
      have hlow := safety _ _ hl (history model xs).length 0 hlpos
      have eh : l = Label.L5 := by
        simpa [past, ho, source, address, sourcePrefix, observedPrefix, stem, block, U] using hhigh
      have el : l = Label.L0 := by
        simpa [past, ho, source, address, sourcePrefix, observedPrefix, stem, block, V] using hlow
      cases eh.symm.trans el
  have outputGrows (v : Configuration × List Label) (h : List Color) :
      v.2.length ≤ (h.foldl evolve v).2.length := by
    induction h generalizing v with
    | nil => exact le_refl _
    | cons c h ih =>
      have one : v.2.length ≤ (evolve v c).2.length := by
        dsimp [evolve]
        simp only [List.length_append]
        exact Nat.le_add_right _ _
      exact one.trans (ih (evolve v c))
  have configurationInj : Set.InjOn (fun xs => (run (history model xs)).1)
      (family : Set (List Return)) := by
    intro xs hx ys hy heq
    have hx' : xs ∈ family := hx
    have hy' : ys ∈ family := hy
    have cutEq : run (history model xs) = run (history model ys) :=
      Prod.ext heq ((emittedEmpty xs hx').trans (emittedEmpty ys hy').symm)
    have commonFuture (n : ℕ) :
        run (front (pairedRecord xs .high) ((history model xs).length + n)) =
        run (front (pairedRecord ys .high) ((history model ys).length + n)) := by
      rw [splice, splice]
      dsimp only [run]
      rw [List.foldl_append, List.foldl_append]
      exact congrArg (fun v =>
        (front (fun p => observe o (coordinate (tailPrefix .high) p) 0) n).foldl evolve v) cutEq
    have actualX := actual xs hx' .high
    have actualY := actual ys hy' .high
    apply actual_source_address_injection .high model xs ys ((weight xs hx').trans (weight ys hy').symm)
    funext p
    obtain ⟨n, hposition⟩ := liveness _ _ actualX.1 actualX.2 p
    have hlong : p < (run (front (pairedRecord xs .high)
        ((history model xs).length + n))).2.length := by
      have hg : (run (front (pairedRecord xs .high) n)).2.length ≤
          (run (front (pairedRecord xs .high) (n + (history model xs).length))).2.length := by
        rw [frontAdd]
        dsimp only [run]
        rw [List.foldl_append]
        exact outputGrows _ _
      rw [Nat.add_comm] at hg
      exact hposition.trans_le hg
    have sameOutput := congrArg Prod.snd (commonFuture n)
    have hyposition : p < (run (front (pairedRecord ys .high)
        ((history model ys).length + n))).2.length := by
      rw [← sameOutput]; exact hlong
    calc
      source .high model xs p =
          (run (front (pairedRecord xs .high) ((history model xs).length + n))).2[p] :=
        (safety _ _ actualX.1 _ p hlong).symm
      _ = (run (front (pairedRecord ys .high) ((history model ys).length + n))).2[p] := by
        simp only [sameOutput]
      _ = source .high model ys p := safety _ _ actualY.1 _ p hyposition
  refine ⟨actual, emittedEmpty, ?_, configurationInj, ?_⟩
  · intro xs hx ys hy hpair
    exact configurationInj hx hy (congrArg Prod.fst hpair)
  · rw [Finset.card_image_of_injOn configurationInj]
    simp


open D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

/-- Exactly the original legal affine source predicate. -/
def OperationOmega (a : ℕ → Label) (x : ℕ → ℝ) : Prop :=
  ∃ path : ℕ → Guard, path 0 = .G0 ∧
    (∀ p, nextGuard (path p) (a p) = some (path (p+1))) ∧
    (∀ p, InSupport (path p) (x p)) ∧
    (∀ p, x p = branch (a p) (x (p+1)))

def OperationRecord (o : Ownership) (b : ℝ) (contract : Contract)
    (a : ℕ → Label) (r : ℕ → Color) : Prop :=
  ∃ x : ℕ → ℝ, OperationOmega a x ∧ ∃ err : ℕ → ℝ,
    ErrorBound b contract err ∧ ∀ p, observe o (x p) (err p) = r p

def OperationFiniteSource (a : ℕ → Label) : Prop := ∃ M : ℕ, ∀ p, M ≤ p → a p = .L0

noncomputable def OperationPairedRecord (model : Model) (o : Ownership) (xs : List Return)
    (j : Side) (p : ℕ) : Color :=
  if hp : p < (history model xs).length then (history model xs)[p]
  else observe o (coordinate (tailPrefix j) (p - (history model xs).length)) 0

/-- Source suppliers are instantiated unchanged; this helper adds no mathematical content. -/
theorem operation_pair_membership (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (xs : List Return) (supply : ActualPairSupply model o b contract xs)
    (j : Side) : OperationRecord o b contract (source j model xs)
      (OperationPairedRecord model o xs j) ∧ OperationFiniteSource (source j model xs) := by
  have reconstruction := paired_source_reconstruction j model xs
  obtain ⟨path,hzero,hedges,hsupport,haffine⟩ :=
    literal_address_path .G0 .G0 (sourcePrefix j model xs) reconstruction.1
  obtain ⟨err,hbound,hslots,hzeroErr,hfuture⟩ := supply j
  have lengths : (observedPrefix j model xs).length = (history model xs).length :=
    reconstruction.2.2.2.2.1.trans reconstruction.2.2.2.2.2.1.symm
  constructor
  · refine ⟨coordinate (sourcePrefix j model xs),⟨path,hzero,hedges,hsupport,haffine⟩,
      err,hbound,?_⟩
    intro p
    by_cases hp : p < (history model xs).length
    · simpa only [OperationPairedRecord,dif_pos hp] using hslots p hp
    · have hge : (history model xs).length ≤ p := Nat.le_of_not_gt hp
      have he : (observedPrefix j model xs).length + (p - (history model xs).length) = p := by
        rw [lengths,Nat.add_sub_of_le hge]
      have hf := hfuture (p - (history model xs).length)
      rw [he] at hf
      simpa only [OperationPairedRecord,dif_neg hp] using hf
  · refine ⟨(sourcePrefix j model xs).length,?_⟩
    intro p hp
    simp only [source,address,List.getElem?_eq_none hp,Option.getD_none]

/-- The exhaustive independent family is the unchanged anonymous45 construction. -/
theorem operation_exact_family (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (N : ℕ) :
    ∃ family : Finset (List Return),
      (∀ xs, xs ∈ family ↔ ActualPairSupply model o b contract xs ∧ listWeight xs = N) ∧
      family.card = Nat.card {xs : List Return //
        ActualPairSupply model o b contract xs ∧ listWeight xs = N} ∧
      Finite {xs : List Return // ActualPairSupply model o b contract xs ∧ listWeight xs = N} := by
  classical
  have lengthBound (w : List CuLetter) : w.length ≤ wordWeight w := by
    induction w with
    | nil => rfl
    | cons l w ih => cases l <;> simp [wordWeight] <;> omega
  have finiteWords (n : ℕ) : Finite {w : List CuLetter // wordWeight w = n} := by
    let f : {w : List CuLetter // wordWeight w = n} → Fin (n + 1) × (Fin n → CuLetter) :=
      fun w => (⟨w.val.length, by have hh := lengthBound w.val; rw [w.property] at hh; omega⟩,
        fun k => w.val[k.val]?.getD .u)
    apply Finite.of_injective f
    intro v w heq
    apply Subtype.ext
    have hlen : v.val.length = w.val.length := congrArg (fun p => p.1.val) heq
    apply List.ext_getElem hlen
    intro i hi hi'
    have hn : i < n := by have hh := lengthBound v.val; rw [v.property] at hh; omega
    have hh := congrFun (congrArg Prod.snd heq) ⟨i, hn⟩
    simpa [f, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] using hh
  let X := {xs : List Return // ActualPairSupply model o b contract xs ∧ listWeight xs = N}
  letI := finiteWords N
  let f : X → {w : List CuLetter // wordWeight w = N} := fun xs =>
    ⟨executionWord xs.val, (complete_execution_word_parser.2.2.2.1 xs.val).trans xs.property.2⟩
  have inj : Function.Injective f := by
    intro v w heq
    apply Subtype.ext
    exact complete_execution_word_parser.2.2.1 (congrArg Subtype.val heq)
  letI : Finite X := Finite.of_injective f inj
  letI : Fintype X := Fintype.ofFinite X
  let family : Finset (List Return) := Finset.univ.image (fun xs : X => xs.val)
  have membership (xs : List Return) :
      xs ∈ family ↔ ActualPairSupply model o b contract xs ∧ listWeight xs = N := by
    constructor
    · intro hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact v.property
    · intro hx
      exact Finset.mem_image.mpr ⟨(⟨xs, hx⟩ : X), Finset.mem_univ _, rfl⟩
  have card : family.card = Nat.card X := by
    calc
      family.card = (Finset.univ : Finset X).card :=
        Finset.card_image_of_injOn (by
          intro v hv w hw heq
          exact Subtype.ext heq)
      _ = Nat.card X := by simp [Nat.card_eq_fintype_card]
  exact ⟨family,membership,card,inferInstance⟩

set_option maxHeartbeats 1000000 in
/-- Finite primitive operations, actual D cuts and the full original code peak separate
all independent paired sources. Universal prose representation is a separate obligation. -/
theorem original_operation_decoder_storage {Configuration : Type*}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (model : Model) (o : Ownership) (b : ℝ) (contract : Contract) (N : ℕ)
    (processing : Processing action initialConfiguration (OperationRecord o b contract))
    (safety : ∀ a r, OperationRecord o b contract a r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, OperationRecord o b contract a r → OperationFiniteSource a → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (encoding : Configuration → List Bool)
    (faithful : Set.InjOn encoding {c | ∃ H,
      ReachThrough action initialConfiguration (OperationRecord o b contract) H c}) :
    let X := {xs : List Return // ActualPairSupply model o b contract xs ∧ listWeight xs = N}
    letI := Classical.decEq Configuration
    ∃ (family : Finset (List Return)) (cuts : X → Frame Configuration Label),
      (∀ xs, xs ∈ family ↔ ActualPairSupply model o b contract xs ∧ listWeight xs = N) ∧
      family.card = Nat.card X ∧
      (∀ x, Cut action initialConfiguration (history model x.val) (cuts x) ∧
        (∀ t, Cut action initialConfiguration (history model x.val) t → t = cuts x) ∧
        (cuts x).acquired = observationOffset model + N ∧ (cuts x).output = [] ∧
        ReachThrough action initialConfiguration (OperationRecord o b contract)
          (observationOffset model + N) (cuts x).state) ∧
      Function.Injective (fun x => (cuts x).state) ∧
      (∃ states : Finset Configuration, states.card = Nat.card X ∧
        ∀ c, c ∈ states ↔ ∃ x, (cuts x).state = c) ∧
      (∀ B : ℕ, Peak action initialConfiguration (OperationRecord o b contract) encoding
        (observationOffset model + N) ≤ (B : WithTop ℕ) → Nat.card X ≤ 2^(B+1)-1) ∧
      (∀ B : ℕ, (∀ x, (encoding (cuts x).state).length = B) → Nat.card X ≤ 2^B) ∧
      Monotone (Peak action initialConfiguration (OperationRecord o b contract) encoding) ∧
      (∀ a r t vertices, OperationRecord o b contract a r →
        Trace action (full r) ⟨initialConfiguration,0,[]⟩ t vertices →
        t.acquired ≤ observationOffset model+N → ∀ c ∈ vertices,
          ((encoding c).length : WithTop ℕ) ≤
            Peak action initialConfiguration (OperationRecord o b contract) encoding
              (observationOffset model+N)) := by
  classical
  dsimp only
  let X := {xs : List Return // ActualPairSupply model o b contract xs ∧ listWeight xs = N}
  obtain ⟨family,membership,card,finite⟩ := operation_exact_family model o b contract N
  letI : Finite X := finite
  letI : Fintype X := Fintype.ofFinite X
  have past (xs : List Return) (j : Side) :
      front (OperationPairedRecord model o xs j) (history model xs).length = history model xs := by
    apply List.ext_getElem (by simp [front])
    intro p hp hq
    simp [front,OperationPairedRecord,hq]
  have existsCut (x : X) : ∃ t, Cut action initialConfiguration (history model x.val) t ∧
      Run action (full (OperationPairedRecord model o x.val .high)) ⟨initialConfiguration,0,[]⟩ t := by
    have actual := operation_pair_membership model o b contract x.val x.property.1 .high
    simpa only [past] using actual_cut_exists action initialConfiguration
      (OperationRecord o b contract) OperationFiniteSource processing liveness
      (source .high model x.val) (OperationPairedRecord model o x.val .high)
      actual.1 actual.2 (history model x.val).length
  let cuts : X → Frame Configuration Label := fun x => Classical.choose (existsCut x)
  have spec (x : X) := Classical.choose_spec (existsCut x)
  have lowRun (x : X) : Run action (full (OperationPairedRecord model o x.val .low))
      ⟨initialConfiguration,0,[]⟩ (cuts x) := by
    obtain ⟨v,hv⟩ := (spec x).1.1
    refine ⟨v,?_⟩
    apply (prefix_trace_iff (OperationPairedRecord model o x.val .low)
      (history model x.val).length (by rw [(spec x).1.2.1])).mpr
    simpa only [past] using hv
  have empty (x : X) : (cuts x).output = [] := by
    have ah := (operation_pair_membership model o b contract x.val x.property.1 .high).1
    have al := (operation_pair_membership model o b contract x.val x.property.1 .low).1
    cases he : (cuts x).output with
    | nil => rfl
    | cons l rest =>
      have hp : 0 < (cuts x).output.length := by simp [he]
      have hh := safety _ _ ah _ (spec x).2 0 hp
      have hl := safety _ _ al _ (lowRun x) 0 hp
      change (cuts x).output[0] = source .high model x.val 0 at hh
      change (cuts x).output[0] = source .low model x.val 0 at hl
      have eh : l = Label.L5 := by
        simpa [he,source,address,sourcePrefix,observedPrefix,stem,block,U] using hh
      have el : l = Label.L0 := by
        simpa [he,source,address,sourcePrefix,observedPrefix,stem,block,V] using hl
      cases eh.symm.trans el
  have injective : Function.Injective (fun x : X => (cuts x).state) := by
    intro x y state
    have ax := operation_pair_membership model o b contract x.val x.property.1 .high
    have ay := operation_pair_membership model o b contract y.val y.property.1 .high
    have same : ∀ j, OperationPairedRecord model o x.val .high ((cuts x).acquired+j) =
        OperationPairedRecord model o y.val .high ((cuts y).acquired+j) := by
      intro j
      rw [(spec x).1.2.1,(spec y).1.2.1]
      simp [OperationPairedRecord,Nat.not_lt.mpr (Nat.le_add_right _ _)]
    have addresses := actual_address_eq action initialConfiguration
      (OperationRecord o b contract) OperationFiniteSource safety liveness
      (source .high model x.val) (source .high model y.val)
      (OperationPairedRecord model o x.val .high) (OperationPairedRecord model o y.val .high)
      ax.1 ay.1 ax.2 (cuts x) (cuts y) (spec x).2 (spec y).2 state
      ((empty x).trans (empty y).symm) same
    apply Subtype.ext
    exact actual_source_address_injection .high model x.val y.val
      (x.property.2.trans y.property.2.symm) addresses
  have reached (x : X) : ReachThrough action initialConfiguration (OperationRecord o b contract)
      (observationOffset model+N) (cuts x).state := by
    refine ⟨source .high model x.val,OperationPairedRecord model o x.val .high,cuts x,
      (operation_pair_membership model o b contract x.val x.property.1 .high).1,(spec x).2,?_,rfl⟩
    have length := (paired_source_reconstruction .high model x.val).2.2.2.2.2.1
    rw [(spec x).1.2.1,length,x.property.2]
  let codes := (Finset.univ : Finset X).image (fun x => encoding (cuts x).state)
  have codeInj : Function.Injective (fun x : X => encoding (cuts x).state) := by
    intro x y eq
    apply injective
    exact faithful ⟨_,reached x⟩ ⟨_,reached y⟩ eq
  have cards : codes.card = Nat.card X := by
    rw [Finset.card_image_of_injOn (by intro x hx y hy he; exact codeInj he)]
    simp [Nat.card_eq_fintype_card]
  refine ⟨family,cuts,membership,card,?_,injective,?_,?_,?_,
    peak_monotone action initialConfiguration (OperationRecord o b contract) encoding,?_⟩
  · intro x
    refine ⟨(spec x).1,(fun t ht => cut_unique action initialConfiguration _ ht (spec x).1),
      ?_,empty x,reached x⟩
    rw [(spec x).1.2.1,(paired_source_reconstruction .high model x.val).2.2.2.2.2.1,x.property.2]
  · refine ⟨(Finset.univ : Finset X).image (fun x => (cuts x).state),?_,?_⟩
    · change ((Finset.univ : Finset X).image (fun x => (cuts x).state)).card = Nat.card X
      rw [Finset.card_image_of_injOn (by intro x hx y hy he; exact injective he)]
      simp [Nat.card_eq_fintype_card]
    · intro c
      change c ∈ ((Finset.univ : Finset X).image (fun x => (cuts x).state)) ↔ ∃ x : X, (cuts x).state = c
      simp only [Finset.mem_image,Finset.mem_univ,true_and]
  · intro B peak
    have lengths : ∀ v ∈ codes, v.length ≤ B := by
      intro v hv
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      have bound := (peak_bound action initialConfiguration (OperationRecord o b contract)
        encoding (observationOffset model+N) (cuts x).state (reached x)).trans peak
      exact_mod_cast bound
    have partition : codes.card = ∑ n ∈ Finset.range (B+1),
        (codes.filter (fun v => v.length = n)).card :=
      Finset.card_eq_sum_card_fiberwise (by
        intro v hv
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (lengths v hv)))
    calc Nat.card X = codes.card := cards.symm
         _ = ∑ n ∈ Finset.range (B+1), (codes.filter (fun v => v.length = n)).card := partition
         _ ≤ ∑ n ∈ Finset.range (B+1), 2^n := by
           apply Finset.sum_le_sum
           intro n hn
           simpa only [Fintype.card_bool] using
             (Finset.card_filter_length_eq_le (T := codes) (s := n))
         _ = 2^(B+1)-1 := by
           simpa using (geom_sum_mul_of_one_le (by norm_num : (1 : ℕ) ≤ 2) (B+1))
  · intro B width
    have eq : codes.filter (fun v => v.length = B) = codes := by
      apply Finset.filter_eq_self.mpr
      intro v hv
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      exact width x
    rw [← cards,← eq]
    simpa only [Fintype.card_bool] using
      (Finset.card_filter_length_eq_le (T := codes) (s := B))

  · intro a r t vertices ha hr hq c hc
    exact peak_trace_bound action initialConfiguration (OperationRecord o b contract) encoding
      (observationOffset model+N) a r t vertices ha hr hq c hc

set_option maxHeartbeats 1000000 in
/-- Actual paired records with a single shared stem force an external prefix tag.
The record hypotheses use the original predicates and assert no decoder separation. -/
theorem original_operation_common_stem {Configuration Z : Type*} [Finite Z]
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (b : ℝ) (contract : Contract)
    (processing : Processing action initialConfiguration (OperationRecord o b contract))
    (safety : ∀ a r, OperationRecord o b contract a r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, OperationRecord o b contract a r → OperationFiniteSource a → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (alpha beta : Z → ℕ → Label) (highRecord lowRecord : Z → ℕ → Color)
    (n : ℕ) (w : List Label)
    (actualHigh : ∀ z, OperationRecord o b contract (alpha z) (highRecord z) ∧
      OperationFiniteSource (alpha z))
    (actualLow : ∀ z, OperationRecord o b contract (beta z) (lowRecord z))
    (past : ∀ z p, p < n → highRecord z p = lowRecord z p)
    (future : ∀ z z' p, highRecord z (n+p) = highRecord z' (n+p))
    (stemHigh : ∀ z i (hi : i < w.length), alpha z i = w[i])
    (stemLow : ∀ z i (hi : i < w.length), beta z i = w[i])
    (different : ∀ z, alpha z w.length ≠ beta z w.length)
    (sourceInjection : Function.Injective alpha) :
    letI := Classical.decEq Configuration
    ∃ (cuts : Z → Frame Configuration Label) (states : Finset Configuration),
      (∀ z, Cut action initialConfiguration (front (highRecord z) n) (cuts z) ∧
        (cuts z).output.length ≤ w.length ∧
        (cuts z).output = w.take (cuts z).output.length ∧
        (cuts z).output <+: w) ∧
      Function.Injective (fun z => ((cuts z).state,(cuts z).output)) ∧
      (∀ c, c ∈ states ↔ ∃ z, (cuts z).state = c) ∧
      Nat.card Z ≤ states.card * (w.length+1) := by
  classical
  letI : Fintype Z := Fintype.ofFinite Z
  have existsCut (z : Z) : ∃ t, Cut action initialConfiguration (front (highRecord z) n) t ∧
      Run action (full (highRecord z)) ⟨initialConfiguration,0,[]⟩ t :=
    actual_cut_exists action initialConfiguration (OperationRecord o b contract)
      OperationFiniteSource processing liveness (alpha z) (highRecord z)
      (actualHigh z).1 (actualHigh z).2 n
  let cuts : Z → Frame Configuration Label := fun z => Classical.choose (existsCut z)
  have spec (z : Z) := Classical.choose_spec (existsCut z)
  have lowRun (z : Z) : Run action (full (lowRecord z)) ⟨initialConfiguration,0,[]⟩ (cuts z) := by
    obtain ⟨v,hv⟩ := (spec z).2
    refine ⟨v,trace_input_transfer hv ?_⟩
    intro q hq hqt
    have eq : (cuts z).acquired = n := by
      have hh : (cuts z).acquired = (front (highRecord z) n).length := (spec z).1.2.1
      simpa only [front,List.length_ofFn] using hh
    dsimp [full]
    rw [past z q (by omega)]
  have bounded (z : Z) : (cuts z).output.length ≤ w.length := by
    by_contra h
    have hp : w.length < (cuts z).output.length := by omega
    have hh := safety _ _ (actualHigh z).1 _ (spec z).2 w.length hp
    have hl := safety _ _ (actualLow z) _ (lowRun z) w.length hp
    exact different z (hh.symm.trans hl)
  have isTake (z : Z) : (cuts z).output = w.take (cuts z).output.length := by
    apply List.ext_getElem (by simp [List.length_take,Nat.min_eq_left (bounded z)])
    intro i hi hi'
    have hw : i < w.length := hi.trans_le (bounded z)
    calc (cuts z).output[i] = alpha z i :=
           safety _ _ (actualHigh z).1 _ (spec z).2 i hi
         _ = beta z i := (stemHigh z i hw).trans (stemLow z i hw).symm
         _ = w[i] := stemLow z i hw
         _ = (w.take (cuts z).output.length)[i] := by simp
  have joint : Function.Injective (fun z => ((cuts z).state,(cuts z).output)) := by
    intro z z' eq
    apply sourceInjection
    apply actual_address_eq action initialConfiguration (OperationRecord o b contract)
      OperationFiniteSource safety liveness (alpha z) (alpha z') (highRecord z) (highRecord z')
      (actualHigh z).1 (actualHigh z').1 (actualHigh z).2 (cuts z) (cuts z')
      (spec z).2 (spec z').2 (congrArg Prod.fst eq) (congrArg Prod.snd eq)
    intro p
    have q : (cuts z).acquired = n := by
      have hh : (cuts z).acquired = (front (highRecord z) n).length := (spec z).1.2.1
      simpa only [front,List.length_ofFn] using hh
    have q' : (cuts z').acquired = n := by
      have hh : (cuts z').acquired = (front (highRecord z') n).length := (spec z').1.2.1
      simpa only [front,List.length_ofFn] using hh
    rw [q,q']
    exact future z z' p
  let states : Finset Configuration := Finset.univ.image (fun z => (cuts z).state)
  have membership (c : Configuration) : c ∈ states ↔ ∃ z, (cuts z).state = c := by
    simp [states]
  let f : Z → {c // c ∈ states} × Fin (w.length+1) := fun z =>
    (⟨(cuts z).state,(membership _).mpr ⟨z,rfl⟩⟩,
      ⟨(cuts z).output.length,Nat.lt_succ_of_le (bounded z)⟩)
  have inj : Function.Injective f := by
    intro z z' he
    apply joint
    have hs : (cuts z).state = (cuts z').state :=
      congrArg (fun p : {c // c ∈ states} × Fin (w.length+1) => p.1.val) he
    have hl : (cuts z).output.length = (cuts z').output.length :=
      congrArg (fun p : {c // c ∈ states} × Fin (w.length+1) => p.2.val) he
    refine Prod.ext hs ?_
    change (cuts z).output = (cuts z').output
    rw [isTake z,isTake z',hl]
  have capacity := Fintype.card_le_of_injective f inj
  refine ⟨cuts,states,?_,joint,membership,?_⟩
  · intro z
    refine ⟨(spec z).1,bounded z,isTake z,?_⟩
    rw [isTake z]
    exact List.take_prefix _ _
  · simpa [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_coe] using capacity


def resetConcatenation (R : Return) : List (List Return) → List Return
  | [] => []
  | xs :: words => (R :: xs) ++ resetConcatenation R words

set_option maxHeartbeats 3000000 in
/-- A fixed full equal-weight weak codebook has one reset and one positive
error margin for all its finite joint concatenations, from either actual start.
Positive cumulative weights recover the choices even when their lengths differ. -/
theorem original_equal_weight_codebook (o : Ownership) (b : ℝ) (K : ℕ)
    (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K))) :
    ∃ R : Return, R.r = 1 ∧ ∀ (sourceModel : Model) (N : ℕ), 0 < N →
    let d := (lam - b) / g ^ 2 / chi ^ K
    let V := {xs : List Return //
      GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs = N}
    Finite V ∧ ∃ eps : ℝ, 0 < eps ∧ 0 < N + (20 + 6*R.m) ∧
      (∀ (targetModel : Model) (words : List (List Return)),
        (∀ xs ∈ words, GuardTrace K d false .high xs (initial .high sourceModel) ∧
          listWeight xs = N) →
        ActualPairSupply targetModel o (b-eps) .closed (resetConcatenation R words) ∧
        (∀ contract : Contract, ActualPairSupply targetModel o b contract
          (resetConcatenation R words)) ∧
        listWeight (resetConcatenation R words) = words.length * (N + (20 + 6*R.m))) ∧
      (∀ (targetModel : Model) (contract : Contract) (q : ℕ),
        Nat.card V ^ q ≤ Nat.card {xs : List Return //
          ActualPairSupply targetModel o b contract xs ∧
          listWeight xs = q * (N + (20 + 6*R.m))}) := by
  classical
  obtain ⟨R,hr,hB,hstrict,hweak,htransfer,hweight,hfirst⟩ :=
    actual_reset_first_return o b K hK hqb hbp
  refine ⟨R,hr,?_⟩
  intro sourceModel N hN
  dsimp only
  let d := (lam - b) / g ^ 2 / chi ^ K
  let V := {xs : List Return //
    GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs = N}
  let A := aSide .high
  let H := hSide .high
  let B := H - rho ^ R.m * (H - chi * A)
  let D := initial .high sourceModel
  have DA : A < D := (actual_complete_boundary_geometry sourceModel []).1 .high 0 |>.1
  have DB : D < B := by
    have hh : D ≤ max (max (xSide .high) (ySide .high)) d := by
      cases sourceModel
      · exact le_trans (le_max_left _ _) (le_max_left _ _)
      · exact le_trans (le_max_right _ _) (le_max_left _ _)
    exact hh.trans_lt hB
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have gp : 0 < g := by dsimp [g,t]; nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  have g1 : g < 1 := by dsimp [g,t]; nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  let delta := B-D
  let gamma := delta * g^N
  have dp : 0 < delta := sub_pos.mpr DB
  have gap : 0 < gamma := mul_pos dp (pow_pos gp N)
  let scale := g^2 * chi^K
  have sp : 0 < scale := mul_pos (pow_pos gp 2) (pow_pos (pow_pos gp 20) K)
  let eps := min ((b - (lam - scale*H))/2) (scale*gamma/4)
  have ep : 0 < eps := lt_min (by dsimp [scale,H] at *; linarith) (by positivity)
  have qe : lam - g^2*chi^K*hSide .high < b-eps := by
    have hh := min_le_left ((b-(lam-scale*H))/2) (scale*gamma/4)
    change eps ≤ (b-(lam-scale*H))/2 at hh
    dsimp [scale,H] at *; linarith
  have pe : b-eps < lam - g^2*chi^K*(aSide .high/(1-rho*chi^K)) := by linarith
  have shiftThreshold : (lam-(b-eps))/g^2/chi^K = d + eps/scale := by
    dsimp [d,scale]; field_simp; ring
  have esmall : eps/scale < gamma := by
    have hh := min_le_right ((b-(lam-scale*H))/2) (scale*gamma/4)
    change eps ≤ scale*gamma/4 at hh
    rw [div_lt_iff₀ sp]
    nlinarith
  have weightAppend (xs ys : List Return) : listWeight (xs++ys) = listWeight xs + listWeight ys := by
    induction xs with
    | nil => simp [listWeight]
    | cons a xs ih => simp only [List.cons_append,listWeight,ih]; omega
  have weightZero (xs : List Return) : listWeight xs = 0 → xs = [] := by
    cases xs with
    | nil => intro _; rfl
    | cons a xs => intro hh; have := a.m_pos; simp only [listWeight] at hh; omega
  have executeAppend (xs ys : List Return) (z : ℝ) :
      execute .high (xs++ys) z = execute .high ys (execute .high xs z) := by
    induction xs generalizing z with
    | nil => rfl
    | cons a xs ih => simp only [List.cons_append,execute,ih]
  have affineDifference (xs : List Return) (x y : ℝ) :
      execute .high xs y - execute .high xs x = g^(listWeight xs)*(y-x) := by
    induction xs generalizing x y with
    | nil => simp [execute,listWeight]
    | cons a xs ih =>
      simp only [execute,listWeight,ih,returnMap]
      have pw : rho^a.m * chi^a.r = g^(6*a.m+20*a.r) := by
        simp only [rho,chi,← pow_mul,← pow_add]
      rw [pow_add]
      calc
        _ = g^(listWeight xs)*(rho^a.m*chi^a.r)*(y-x) := by ring
        _ = _ := by rw [pw]; ring
  have positions (xs : List Return) (threshold z : ℝ) (st : Bool) :
      GuardTrace K threshold st .high xs z ↔
      ∀ i : Fin xs.length, xs[i].r ≤ K ∧
        (xs[i].r = K → if st then threshold < execute .high (xs.take i.val) z
          else threshold ≤ execute .high (xs.take i.val) z) := by
    induction xs generalizing z with
    | nil => simp [GuardTrace]
    | cons a xs ih =>
      rw [GuardTrace,ih]
      constructor
      · rintro ⟨hc,hg,ht⟩ ⟨i,hi⟩
        cases i with
        | zero => simpa [execute] using And.intro hc hg
        | succ i => simpa [execute] using ht ⟨i,by simpa using hi⟩
      · intro ht
        have hh := ht ⟨0,by simp⟩
        refine ⟨by simpa using hh.1,by simpa [execute] using hh.2,?_⟩
        intro i; simpa [execute] using ht ⟨i.val+1,by simpa using i.isLt⟩
  have improve (xs : List Return)
      (hw : GuardTrace K d false .high xs D) (wn : listWeight xs = N)
      (E : ℝ) (hE : B ≤ E) :
      GuardTrace K ((lam-(b-eps))/g^2/chi^K) true .high xs E ∧
      A < execute .high xs E := by
    have ED : D < E := DB.trans_le hE
    constructor
    · apply (positions _ _ _ _).mpr
      intro i
      have hh := (positions _ _ _ _).mp hw i
      refine ⟨hh.1,?_⟩
      intro hi
      have wd : listWeight (xs.take i.val) ≤ N := by
        have ww := weightAppend (xs.take i.val) (xs.drop i.val)
        rw [List.take_append_drop,wn] at ww; omega
      have pg : g^N ≤ g^(listWeight (xs.take i.val)) :=
        pow_le_pow_of_le_one gp.le g1.le wd
      have gain : gamma ≤ execute .high (xs.take i.val) E - execute .high (xs.take i.val) D := by
        rw [affineDifference]
        have dd : delta ≤ E-D := by dsimp [delta]; linarith
        change delta*g^N ≤ g^(listWeight (xs.take i.val))*(E-D)
        calc delta*g^N ≤ delta*g^(listWeight (xs.take i.val)) := mul_le_mul_of_nonneg_left pg dp.le
             _ ≤ g^(listWeight (xs.take i.val))*(E-D) := by
               simpa only [mul_comm] using mul_le_mul_of_nonneg_left dd (pow_pos gp (listWeight (xs.take i.val))).le
      have old := hh.2 hi
      simp only [Bool.false_eq_true,if_false] at old
      simp only [Bool.true_eq,if_true]
      rw [shiftThreshold]
      linarith
    · have base := (actual_complete_boundary_geometry sourceModel xs).1 .high xs.length
      simp only [List.take_length] at base
      have pos := mul_pos (pow_pos gp (listWeight xs)) (sub_pos.mpr ED)
      rw [← affineDifference] at pos
      have ba : A < execute .high xs D := base.1
      linarith
  have traceAppend (xs ys : List Return) (z threshold : ℝ) :
      GuardTrace K threshold true .high (xs++ys) z ↔
      GuardTrace K threshold true .high xs z ∧
      GuardTrace K threshold true .high ys (execute .high xs z) := by
    induction xs generalizing z with
    | nil => simp [GuardTrace,execute]
    | cons a xs ih => simp only [List.cons_append,GuardTrace,execute,ih]; tauto
  have joint (words : List (List Return))
      (hw : ∀ xs ∈ words, GuardTrace K d false .high xs D ∧ listWeight xs = N)
      (E : ℝ) (hE : A < E) :
      GuardTrace K ((lam-(b-eps))/g^2/chi^K) true .high (resetConcatenation R words) E := by
    induction words generalizing E with
    | nil => trivial
    | cons xs words ih =>
      obtain ⟨ht,wn⟩ := hw xs (by simp)
      have im := improve xs ht wn (returnMap .high R E) (hweak E hE.le)
      apply (traceAppend _ _ _ _).mpr
      refine ⟨⟨by rw [hr]; omega,?_,im.1⟩,?_⟩
      · intro hk; omega
      · apply ih (by intro x hx; exact hw x (by simp [hx]))
        simpa only [execute] using im.2
  have uniform (targetModel : Model) (words : List (List Return))
      (hw : ∀ xs ∈ words, GuardTrace K d false .high xs D ∧ listWeight xs = N) :
      ActualPairSupply targetModel o (b-eps) .closed (resetConcatenation R words) ∧
      (∀ contract : Contract, ActualPairSupply targetModel o b contract (resetConcatenation R words)) ∧
      listWeight (resetConcatenation R words) = words.length*(N+(20+6*R.m)) := by
    have tr := joint words hw (initial .high targetModel)
      ((actual_complete_boundary_geometry targetModel []).1 .high 0).1
    have supply := (actual_strict_record_supply targetModel o (b-eps)
      (resetConcatenation R words) K hK qe pe).1.mpr tr
    have closed : ActualPairSupply targetModel o (b-eps) .closed (resetConcatenation R words) := by
      intro j
      obtain ⟨err,he,hh,hz,hf⟩ := supply j
      exact ⟨err,fun p => (he p).le,hh,hz,hf⟩
    refine ⟨closed,?_,?_⟩
    · intro contract j
      obtain ⟨err,he,hh,hz,hf⟩ := closed j
      refine ⟨err,?_,hh,hz,hf⟩
      cases contract with
      | closed => exact fun p => (he p).trans (by linarith)
      | strict => exact fun p => (he p).trans_lt (by linarith)
      | recordMargin => exact ⟨eps,ep,he⟩
    · clear tr supply closed
      induction words with
      | nil => simp [resetConcatenation,listWeight]
      | cons xs words ih =>
        have wn := (hw xs (by simp)).2
        have htail := ih (by intro x hx; exact hw x (by simp [hx]))
        rw [resetConcatenation,weightAppend,hweight xs,wn,htail,List.length_cons]
        ring
  have finite : Finite V := by
    obtain ⟨family,hm,hc,hf⟩ := operation_exact_family sourceModel o b .strict (N+(20+6*R.m))
    letI := hf
    let f : V → {xs : List Return // ActualPairSupply sourceModel o b .strict xs ∧
        listWeight xs = N+(20+6*R.m)} := fun xs =>
      ⟨R::xs.val,htransfer sourceModel sourceModel xs.val xs.property.1,
        by rw [hweight,xs.property.2]; omega⟩
    exact Finite.of_injective f (by intro x y h; apply Subtype.ext; exact List.cons.inj (congrArg Subtype.val h) |>.2)
  letI : Finite V := finite
  have firstBlock (xs ys tx ty : List Return) (wx : listWeight xs = N) (wy : listWeight ys = N)
      (he : (R::xs)++tx = (R::ys)++ty) : xs=ys := by
    rcases List.append_eq_append_iff.mp he with ⟨as,ha,ht⟩ | ⟨bs,hb,ht⟩
    · have wz : listWeight as = 0 := by
        have hh := congrArg listWeight ha
        rw [weightAppend,hweight,hweight,wx,wy] at hh; omega
      have zz := weightZero as wz
      simpa [zz] using (List.cons.inj ha).2.symm
    · have wz : listWeight bs = 0 := by
        have hh := congrArg listWeight hb
        rw [weightAppend,hweight,hweight,wx,wy] at hh; omega
      have zz := weightZero bs wz
      simpa [zz] using (List.cons.inj hb).2
  have concatInjective (words words' : List (List Return))
      (hw : ∀ xs ∈ words, listWeight xs=N)
      (hw' : ∀ xs ∈ words', listWeight xs=N)
      (he : resetConcatenation R words = resetConcatenation R words') : words=words' := by
    induction words generalizing words' with
    | nil => cases words' <;> simp_all [resetConcatenation]
    | cons xs words ih =>
      cases words' with
      | nil => simp [resetConcatenation] at he
      | cons ys words' =>
        have xy := firstBlock xs ys _ _ (hw xs (by simp)) (hw' ys (by simp)) he
        subst ys
        have ht : resetConcatenation R words = resetConcatenation R words' :=
          List.append_cancel_left (by simpa only [resetConcatenation] using he)
        congr 1
        exact ih words' (by intro x hx; exact hw x (by simp [hx]))
          (by intro x hx; exact hw' x (by simp [hx])) ht
  refine ⟨finite,eps,ep,by omega,uniform,?_⟩
  intro targetModel contract q
  let f : (Fin q → V) → {xs : List Return // ActualPairSupply targetModel o b contract xs ∧
      listWeight xs = q*(N+(20+6*R.m))} := fun z =>
    ⟨resetConcatenation R (List.ofFn (fun i => (z i).val)), by
      have hw : ∀ xs ∈ List.ofFn (fun i => (z i).val),
          GuardTrace K d false .high xs D ∧ listWeight xs=N := by
        intro xs hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact (z i).property
      have uu := uniform targetModel (List.ofFn (fun i => (z i).val)) hw
      exact ⟨uu.2.1 contract,by simpa using uu.2.2⟩⟩
  have inj : Function.Injective f := by
    intro z z' he
    have hw (u : Fin q → V) : ∀ xs ∈ List.ofFn (fun i => (u i).val), listWeight xs=N := by
      intro xs hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact (u i).property.2
    have lists := concatInjective _ _ (hw z) (hw z') (congrArg Subtype.val he)
    funext i
    apply Subtype.ext
    have hh := congrArg (fun l => l[i.val]?) lists
    simpa using hh
  obtain ⟨family,hm,hc,hf⟩ := operation_exact_family targetModel o b contract (q*(N+(20+6*R.m)))
  letI := hf
  have card := Nat.card_le_card_of_injective f inj
  simpa [Nat.card_fun,Nat.card_fin] using card


open D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open Filter
open scoped Topology

set_option maxHeartbeats 2000000 in
/-- One reset works at all weights. Every fixed nonempty full weak codebook
forces its exact-denominator coefficient in the full storage liminf, including
infinite peaks. Startup is derived from the actual first-label competitors. -/
theorem original_codebook_storage_liminf {Configuration : Type*}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (b : ℝ) (contract : Contract) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K)))
    (safety : ∀ a r, OperationRecord o b contract a r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, OperationRecord o b contract a r → OperationFiniteSource a → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (postprocessing : ∀ a r, OperationRecord o b contract a r →
      ∀ (c d : Configuration) (q : ℕ) (out batch : List Label)
        (f : Color → Option (Configuration × List Label)),
      Run action (full r) ⟨initialConfiguration,0,[]⟩ ⟨c,q,out⟩ →
      action c = .acquire f → f (r q) = some (d,batch) →
      ∃ t, Drain action ⟨d,q+1,out++batch⟩ t)
    (encoding : Configuration → List Bool)
    (faithful : Set.InjOn encoding {c | ∃ H,
      ReachThrough action initialConfiguration (OperationRecord o b contract) H c}) :
    ∃ R : Return, R.r = 1 ∧ ∀ (sourceModel : Model) (N : ℕ), 0 < N →
      let a := Nat.card {xs : List Return //
        GuardTrace K ((lam-b)/g^2/chi^K) false .high xs (initial .high sourceModel) ∧
        listWeight xs = N}
      1 ≤ a → ∀ model : Model,
      let L := N+(20+6*R.m)
      let fullPeak := Peak action initialConfiguration (OperationRecord o b contract) encoding
      (∀ H B : ℕ, observationOffset model ≤ H → fullPeak H ≤ (B : WithTop ℕ) →
        (((H-observationOffset model)/L : ℕ) : ℝ)*Real.logb 2 (a : ℝ)-1 ≤ B) ∧
      ENNReal.ofReal (Real.logb 2 (a : ℝ)/(L : ℝ)) ≤
        liminf (fun H : ℕ => ENat.toENNReal (fullPeak H)/(H : ENNReal)) atTop := by
  classical
  obtain ⟨R,hr,books⟩ := original_equal_weight_codebook o b K hK hqb hbp
  refine ⟨R,hr,?_⟩
  intro sourceModel N hN
  dsimp only
  let V := {xs : List Return //
    GuardTrace K ((lam-b)/g^2/chi^K) false .high xs (initial .high sourceModel) ∧
    listWeight xs=N}
  let a := Nat.card V
  intro ha model
  let L := N+(20+6*R.m)
  let Delta := observationOffset model
  let fullPeak := Peak action initialConfiguration (OperationRecord o b contract) encoding
  obtain ⟨finite,eps,ep,Lpos,uniform,count⟩ := books sourceModel N hN
  have emptySupply : ActualPairSupply model o b contract [] := by
    have hh := uniform model [] (by simp)
    simpa [resetConcatenation] using hh.2.1 contract
  have high := operation_pair_membership model o b contract [] emptySupply .high
  have low := operation_pair_membership model o b contract [] emptySupply .low
  have different : source .high model [] 0 ≠ source .low model [] 0 := by
    simp [source,address,sourcePrefix,observedPrefix,stem,block,U,FibonacciLiteralSource.V]
  have processing := processing_of_safe_live_pair action initialConfiguration
    (OperationRecord o b contract) OperationFiniteSource safety liveness
    (source .high model []) (source .low model [])
    (OperationPairedRecord model o [] .high) (OperationPairedRecord model o [] .low)
    high.1 low.1 high.2 different postprocessing
  have mono : Monotone fullPeak :=
    peak_monotone action initialConfiguration (OperationRecord o b contract) encoding
  have capacity (q B : ℕ) (hp : fullPeak (Delta+q*L) ≤ (B : WithTop ℕ)) :
      a^q ≤ 2^(B+1)-1 := by
    obtain ⟨family,cuts,hm,hc,hcut,hinj,hstates,hcap,hfixed,hmono,hvertices⟩ :=
      original_operation_decoder_storage action initialConfiguration model o b contract (q*L)
        processing safety liveness encoding faithful
    exact (count model contract q).trans (hcap B hp)
  have lp : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Lpos
  have ap : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ha)
  let loga := Real.logb 2 (a : ℝ)
  have lognonneg : 0 ≤ loga := Real.logb_nonneg (by norm_num) (by exact_mod_cast ha)
  have finiteFloor (H B : ℕ) (hH : Delta ≤ H) (hp : fullPeak H ≤ (B : WithTop ℕ)) :
      (((H-Delta)/L : ℕ) : ℝ)*loga-1 ≤ (B : ℝ) := by
    let q := (H-Delta)/L
    have lower : Delta+q*L ≤ H := by
      have hh := Nat.div_mul_le_self (H-Delta) L
      dsimp [q]; omega
    have cn : a^q ≤ 2^(B+1) := (capacity q B ((mono lower).trans hp)).trans (Nat.sub_le _ _)
    have cr : (a : ℝ)^q ≤ (2 : ℝ)^(B+1) := by exact_mod_cast cn
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2) (pow_pos ap q) cr
    simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one,
      Nat.cast_add,Nat.cast_one] at hl
    change (q : ℝ)*loga-1 ≤ (B : ℝ)
    dsimp [loga] at *; linarith
  refine ⟨finiteFloor,?_⟩
  let slope := loga/(L : ℝ)
  let loss := (((Delta : ℝ)+(L : ℝ))*loga+(L : ℝ))/(L : ℝ)
  have lowerReal (H B : ℕ) (hH : max Delta 1 ≤ H) (hp : fullPeak H ≤ (B : WithTop ℕ)) :
      slope-loss/(H : ℝ) ≤ (B : ℝ)/(H : ℝ) := by
    have Hpos : (0 : ℝ)<(H : ℝ) := by exact_mod_cast (show 0<H by omega)
    have hd : Delta≤H := by omega
    let q := (H-Delta)/L
    have Lpos' : 0<L := Lpos
    have remainder := Nat.mod_lt (H-Delta) Lpos'
    have decomp : (H-Delta)/L*L+(H-Delta)%L = H-Delta := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod (H-Delta) L
    have bound : H ≤ Delta+q*L+L := by dsimp [q]; omega
    have br : (H : ℝ) ≤ (Delta : ℝ)+(q : ℝ)*(L : ℝ)+(L : ℝ) := by exact_mod_cast bound
    have mulbound := mul_le_mul_of_nonneg_right br lognonneg
    have floor := finiteFloor H B hd hp
    have interpolate : slope*(H : ℝ)-loss ≤ (q : ℝ)*loga-1 := by
      have identity : slope*(H : ℝ)-loss =
          (loga*(H : ℝ)-(((Delta : ℝ)+(L : ℝ))*loga+(L : ℝ)))/(L : ℝ) := by
        dsimp [slope,loss]; ring
      rw [identity,div_le_iff₀ lp]
      nlinarith only [mulbound]
    have identity : slope-loss/(H : ℝ) = (slope*(H : ℝ)-loss)/(H : ℝ) := by
      field_simp
    rw [identity,div_le_div_iff_of_pos_right Hpos]
    exact interpolate.trans floor
  have eventual : ∀ᶠ H : ℕ in atTop,
      ENNReal.ofReal (slope-loss/(H : ℝ)) ≤ ENat.toENNReal (fullPeak H)/(H : ENNReal) := by
    filter_upwards [eventually_ge_atTop (max Delta 1)] with H hH
    have Hpos : (0 : ℝ)<(H : ℝ) := by exact_mod_cast (show 0<H by omega)
    rcases eq_or_ne (fullPeak H) ⊤ with ht | hf
    · rw [ht]
      change ENNReal.ofReal (slope-loss/(H : ℝ)) ≤ (⊤ : ENNReal)/(H : ENNReal)
      rw [ENNReal.top_div_of_ne_top (by simp)]
      exact le_top
    · obtain ⟨B,hB⟩ := WithTop.ne_top_iff_exists.mp hf
      have rr := lowerReal H B hH (by rw [← hB]; exact le_rfl)
      have er := ENNReal.ofReal_le_ofReal rr
      rw [← hB]
      change ENNReal.ofReal (slope-loss/(H : ℝ)) ≤ (B : ENNReal)/(H : ENNReal)
      simpa [ENNReal.ofReal_div_of_pos Hpos] using er
  have conv : Tendsto (fun H : ℕ => ENNReal.ofReal (slope-loss/(H : ℝ))) atTop
      (𝓝 (ENNReal.ofReal slope)) := by
    apply ENNReal.tendsto_ofReal
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat loss)
  change ENNReal.ofReal slope ≤ _
  rw [← conv.liminf_eq]
  exact liminf_le_liminf eventual


set_option maxHeartbeats 2000000 in
/-- Full actual-source peak storage has the necessary lower-limit coefficient
of the original weak-list rate. Fixed-codebook bounds are taken before the
codebook weight tends to infinity; no common margin across weights is used. -/
theorem original_complete_storage_liminf {Configuration : Type*}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (b : ℝ) (contract : Contract) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K)))
    (safety : ∀ a r, OperationRecord o b contract a r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, OperationRecord o b contract a r → OperationFiniteSource a → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (postprocessing : ∀ a r, OperationRecord o b contract a r →
      ∀ (c d : Configuration) (q : ℕ) (out batch : List Label)
        (f : Color → Option (Configuration × List Label)),
      Run action (full r) ⟨initialConfiguration,0,[]⟩ ⟨c,q,out⟩ →
      action c = .acquire f → f (r q) = some (d,batch) →
      ∃ t, Drain action ⟨d,q+1,out++batch⟩ t)
    (encoding : Configuration → List Bool)
    (faithful : Set.InjOn encoding {c | ∃ H,
      ReachThrough action initialConfiguration (OperationRecord o b contract) H c}) :
    ∀ sourceModel : Model,
    let W (n : ℕ) := Nat.card {xs : List Return //
      GuardTrace K ((lam-b)/g^2/chi^K) false .high xs (initial .high sourceModel) ∧
      listWeight xs=n}
    ENNReal.ofReal (limsup (fun n : ℕ =>
      Real.logb 2 ((max 1 (W n) : ℕ) : ℝ)/(n : ℝ)) atTop) ≤
      liminf (fun H : ℕ => ENat.toENNReal
        (Peak action initialConfiguration (OperationRecord o b contract) encoding H)/
        (H : ENNReal)) atTop := by
  classical
  obtain ⟨R,hr,codebooks⟩ := original_codebook_storage_liminf action initialConfiguration
    o b contract K hK hqb hbp safety liveness postprocessing encoding faithful
  intro sourceModel
  dsimp only
  let W (n : ℕ) := Nat.card {xs : List Return //
    GuardTrace K ((lam-b)/g^2/chi^K) false .high xs (initial .high sourceModel) ∧
    listWeight xs=n}
  let r (n : ℕ) := Real.logb 2 ((max 1 (W n) : ℕ) : ℝ)/(n : ℝ)
  let C_R := 20+6*R.m
  let s (n : ℕ) := Real.logb 2 ((max 1 (W n) : ℕ) : ℝ)/((n+C_R : ℕ) : ℝ)
  let c := liminf (fun H : ℕ => ENat.toENNReal
    (Peak action initialConfiguration (OperationRecord o b contract) encoding H)/(H : ENNReal)) atTop
  change ENNReal.ofReal (limsup r atTop) ≤ c
  by_cases hc : c=⊤
  · rw [hc]; exact le_top
  have common (n : ℕ) (hn : 0<n) : ENNReal.ofReal (s n) ≤ c := by
    by_cases ha : 1≤W n
    · simpa only [W,C_R,s,max_eq_right ha] using (codebooks sourceModel n hn ha .original).2
    · have hz : W n=0 := by omega
      simp [s,hz]
  have logpos (n : ℕ) : 0 ≤ Real.logb 2 ((max 1 (W n) : ℕ) : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (Nat.le_max_left 1 (W n)))
  have rpos (n : ℕ) : 0≤r n := div_nonneg (logpos n) (by positivity)
  have crpos : 0≤c.toReal := ENNReal.toReal_nonneg
  have rb : IsBoundedUnder (· ≤ ·) atTop r := by
    apply isBoundedUnder_of_eventually_le (a := c.toReal*(1+(C_R : ℝ)))
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have np : (0 : ℝ)<(n : ℝ) := by exact_mod_cast hn
    have n1 : (1 : ℝ)≤(n : ℝ) := by exact_mod_cast hn
    have ncp : (0 : ℝ)<((n+C_R : ℕ) : ℝ) := by exact_mod_cast (show 0<n+C_R by omega)
    have cp : 0≤(C_R : ℝ) := by positivity
    have h := (ENNReal.ofReal_le_iff_le_toReal hc).mp (common n hn)
    dsimp [s] at h
    rw [div_le_iff₀ ncp] at h
    push_cast at h
    dsimp [r]
    rw [div_le_iff₀ np]
    have gain := mul_nonneg (mul_nonneg crpos cp) (sub_nonneg.mpr n1)
    push_cast
    nlinarith only [h,gain]
  let v (n : ℕ) : ℝ := (n : ℝ)/((n+C_R : ℕ) : ℝ)
  have vp : ∀ᶠ n in atTop, 0≤v n := Eventually.of_forall fun n => by dsimp [v]; positivity
  have vb : IsBoundedUnder (· ≤ ·) atTop v := by
    apply isBoundedUnder_of_eventually_le (a := (1 : ℝ))
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have np : (0 : ℝ)<((n+C_R : ℕ) : ℝ) := by exact_mod_cast (show 0<n+C_R by omega)
    dsimp [v]
    rw [div_le_iff₀ np,one_mul]
    exact_mod_cast Nat.le_add_right n C_R
  have vt : Tendsto v atTop (𝓝 1) := by
    simpa only [v,Nat.cast_add] using tendsto_natCast_div_add_atTop (C_R : ℝ)
  have products : (r*v) =ᶠ[atTop] s := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have np : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
    dsimp [r,v,s]
    field_simp
  have prodNonneg : ∃ᶠ n in atTop, 0≤(r*v) n :=
    (Frequently.of_forall rpos).and_eventually vp |>.mono (fun n h => mul_nonneg h.1 h.2)
  have prodBound : ∀ᶠ n in atTop, (r*v) n ≤ c.toReal := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),products] with n hn he
    rw [he]
    exact (ENNReal.ofReal_le_iff_le_toReal hc).mp (common n hn)
  have upper : limsup (r*v) atTop ≤ c.toReal :=
    limsup_le_of_le (IsCoboundedUnder.of_frequently_ge prodNonneg) prodBound
  have lower := le_limsup_mul (Frequently.of_forall rpos) rb vp vb
  rw [vt.liminf_eq,mul_one] at lower
  have result := ENNReal.ofReal_le_ofReal (lower.trans upper)
  simpa only [ENNReal.ofReal_toReal hc] using result


set_option maxHeartbeats 1000000 in
/-- An interval retains its actual endpoint membership. Positive contractions
may approach an excluded fixed endpoint; negative contractions require the
first two actual members and hence the fixed point itself. -/
theorem competing_tail_orbit_criterion (T : Set ℝ) (hT : T.OrdConnected)
    (a y : ℝ) (ha : -1<a) (ha1 : a<1) (hane : a≠0) :
    let F := fun x : ℝ => y+a*(x-y)
    (∀ x, (∀ n : ℕ, F^[n] x ∈ T) ↔
      if 0<a then x∈T ∧ y∈closure T else x∈T ∧ F x∈T) ∧
    ({x : ℝ | ∀ n : ℕ, F^[n] x∈T}.Nonempty ↔
      if 0<a then T.Nonempty ∧ y∈closure T else y∈T) := by
  let F := fun x : ℝ => y+a*(x-y)
  have formula (x : ℝ) (n : ℕ) : F^[n] x = y+a^n*(x-y) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply',ih,pow_succ]; dsimp [F]; ring
  by_cases apos : 0<a
  · simp only [if_pos apos]
    have criterion (x : ℝ) : (∀ n : ℕ, F^[n] x∈T) ↔ x∈T ∧ y∈closure T := by
      constructor
      · intro orbit
        have conv : Tendsto (fun n : ℕ => F^[n] x) atTop (𝓝 y) := by
          have ht := tendsto_pow_atTop_nhds_zero_of_lt_one apos.le ha1
          simpa only [formula,zero_mul,add_zero] using tendsto_const_nhds.add (ht.mul_const (x-y))
        exact ⟨by simpa using orbit 0,mem_closure_of_tendsto conv (Eventually.of_forall orbit)⟩
      · rintro ⟨hx,hy⟩ n
        cases n with
        | zero => simpa using hx
        | succ n =>
          rw [formula]
          let z := y+a^(n+1)*(x-y)
          have qp : 0<a^(n+1) := pow_pos apos _
          have ql : a^(n+1)<1 := pow_lt_one₀ apos.le ha1 (by omega)
          rcases lt_trichotomy x y with xy | xy | yx
          · have xz : x<z := by
              have hh := mul_pos (sub_pos.mpr ql) (sub_pos.mpr xy)
              dsimp [z]; nlinarith
            have zy : z<y := by
              have hh := mul_pos qp (sub_pos.mpr xy)
              dsimp [z]; nlinarith
            obtain ⟨w,zw,hw⟩ := mem_closure_iff.1 hy (Set.Ioi z) isOpen_Ioi zy
            exact hT.out hx hw ⟨xz.le,zw.le⟩
          · subst x; simpa [z] using hx
          · have yz : y<z := by
              have hh := mul_pos qp (sub_pos.mpr yx)
              dsimp [z]; nlinarith
            have zx : z<x := by
              have hh := mul_pos (sub_pos.mpr ql) (sub_pos.mpr yx)
              dsimp [z]; nlinarith
            obtain ⟨w,wz,hw⟩ := mem_closure_iff.1 hy (Set.Iio z) isOpen_Iio yz
            exact hT.out hw hx ⟨wz.le,zx.le⟩
    refine ⟨criterion,?_⟩
    constructor
    · rintro ⟨x,hx⟩; exact ⟨⟨x,(criterion x).mp hx |>.1⟩,(criterion x).mp hx |>.2⟩
    · rintro ⟨⟨x,hx⟩,hy⟩; exact ⟨x,(criterion x).mpr ⟨hx,hy⟩⟩
  · have aneg : a<0 := lt_of_le_of_ne (le_of_not_gt apos) hane
    simp only [if_neg apos]
    have anti : Antitone F := by
      intro x z hxz
      have hh := mul_le_mul_of_nonpos_left hxz aneg.le
      dsimp [F]; linarith
    have square : a^2≤1 := by nlinarith
    have twice (x : ℝ) : F (F x) = y+a^2*(x-y) := by dsimp [F]; ring
    have middle (x : ℝ) : y∈Set.uIcc x (F x) := by
      by_cases xy : x≤y
      · have hp := mul_nonneg_of_nonpos_of_nonpos aneg.le (sub_nonpos.mpr xy)
        have yf : y≤F x := by dsimp [F]; linarith
        exact ⟨(min_le_left _ _).trans xy,yf.trans (le_max_right _ _)⟩
      · have yx : y≤x := le_of_not_ge xy
        have hp := mul_nonpos_of_nonpos_of_nonneg aneg.le (sub_nonneg.mpr yx)
        have fy : F x≤y := by dsimp [F]; linarith
        exact ⟨(min_le_right _ _).trans fy,yx.trans (le_max_left _ _)⟩
    have invariant (x z : ℝ) (hz : z∈Set.uIcc x (F x)) : F z∈Set.uIcc x (F x) := by
      by_cases xy : x≤y
      · have hp := mul_nonneg_of_nonpos_of_nonpos aneg.le (sub_nonpos.mpr xy)
        have yf : y≤F x := by dsimp [F]; linarith
        have xf : x≤F x := xy.trans yf
        change min x (F x)≤z ∧ z≤max x (F x) at hz
        change min x (F x)≤F z ∧ F z≤max x (F x)
        rw [min_eq_left xf,max_eq_right xf] at hz ⊢
        have hh := mul_le_mul_of_nonpos_right square (sub_nonpos.mpr xy)
        have xx : x≤F (F x) := by rw [twice]; nlinarith
        exact ⟨xx.trans (anti hz.2),anti hz.1⟩
      · have yx : y≤x := le_of_not_ge xy
        have hp := mul_nonpos_of_nonpos_of_nonneg aneg.le (sub_nonneg.mpr yx)
        have fy : F x≤y := by dsimp [F]; linarith
        have fx : F x≤x := fy.trans yx
        change min x (F x)≤z ∧ z≤max x (F x) at hz
        change min x (F x)≤F z ∧ F z≤max x (F x)
        rw [min_eq_right fx,max_eq_left fx] at hz ⊢
        have hh := mul_le_mul_of_nonneg_right square (sub_nonneg.mpr yx)
        have xx : F (F x)≤x := by rw [twice]; nlinarith
        exact ⟨anti hz.2,(anti hz.1).trans xx⟩
    have criterion (x : ℝ) : (∀ n : ℕ, F^[n] x∈T) ↔ x∈T ∧ F x∈T := by
      constructor
      · intro orbit; exact ⟨by simpa using orbit 0,by simpa using orbit 1⟩
      · rintro ⟨hx,hf⟩ n
        apply hT.uIcc_subset hx hf
        induction n with
        | zero => simp
        | succ n ih => rw [Function.iterate_succ_apply']; exact invariant x _ ih
    refine ⟨criterion,?_⟩
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨hx,hf⟩ := (criterion x).mp hx
      exact hT.uIcc_subset hx hf (middle x)
    · intro hy
      refine ⟨y,(criterion y).mpr ⟨hy,?_⟩⟩
      simpa [F] using hy


open scoped Topology
set_option maxHeartbeats 1000000

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open Filter Topology

private theorem tail_arithmetic :
    t ^ 2 = 1 - t ∧ 0 < t ∧ t < 1 ∧ 0 < g ∧ g < 1 ∧ 1 < phi := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsn := Real.sqrt_nonneg (5 : ℝ)
  have htq : t ^ 2 = 1 - t := by dsimp [t]; nlinarith
  have htp : 0 < t := by dsimp [t]; nlinarith
  have ht1 : t < 1 := by dsimp [t]; nlinarith
  have hgp : 0 < g := by dsimp [g, t]; nlinarith
  have hg1 : g < 1 := by dsimp [g]; linarith
  exact ⟨htq, htp, ht1, hgp, hg1, by dsimp [phi]; linarith⟩

/-- Closed branch images cover each literal guard support, including endpoints. -/
private theorem inverse_branch (s : Guard) (z : ℝ) (hz : InSupport s z) :
    ∃ (l : Label) (e : Guard) (z' : ℝ),
      nextGuard s l = some e ∧ InSupport e z' ∧ z = branch l z' := by
  rcases tail_arithmetic with ⟨htq, htp, ht1, hgp, hg1, hphi⟩
  have inverse (l : Label) (e : Guard)
      (hlo : shift l - g * supportUpper e ≤ z)
      (hhi : z ≤ shift l + g) :
      InSupport e ((shift l - z) / g) ∧
        z = branch l ((shift l - z) / g) := by
    refine ⟨⟨(le_div_iff₀ hgp).2 ?_, (div_le_iff₀ hgp).2 ?_⟩, ?_⟩
    · linarith
    · linarith
    · dsimp [branch]
      have hc : g * ((shift l - z) / g) = shift l - z := by
        rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hgp)]
      rw [hc]
      ring
  rcases hz with ⟨hzlo, hzhi⟩
  cases s with
  | G0 =>
    change z ≤ 1 + t at hzhi
    by_cases h3 : z ≤ t - 1
    · refine ⟨.L3, .G0, (shift .L3 - z) / g, rfl, ?_⟩
      apply inverse <;> dsimp [shift, supportUpper, g, phi] <;> nlinarith
    have h3' : t - 1 < z := lt_of_not_ge h3
    by_cases h0 : z ≤ 2 * t - 1
    · refine ⟨.L0, .G0, (shift .L0 - z) / g, rfl, ?_⟩
      apply inverse <;> dsimp [shift, supportUpper, g, phi] <;> nlinarith
    have h0' : 2 * t - 1 < z := lt_of_not_ge h0
    by_cases h5 : z ≤ t
    · refine ⟨.L5, .G1, (shift .L5 - z) / g, rfl, ?_⟩
      apply inverse <;> dsimp [shift, supportUpper, g, T2] <;> nlinarith
    have h5' : t < z := lt_of_not_ge h5
    by_cases h2 : z ≤ 2 * t
    · refine ⟨.L2, .G0, (shift .L2 - z) / g, rfl, ?_⟩
      apply inverse <;> dsimp [shift, supportUpper, g, phi] <;> nlinarith
    have h2' : 2 * t < z := lt_of_not_ge h2
    refine ⟨.L25, .G1, (shift .L25 - z) / g, rfl, ?_⟩
    apply inverse <;> dsimp [shift, supportUpper, g] <;> nlinarith
  | G1 =>
    change z ≤ t at hzhi
    by_cases h3 : z ≤ t - 1
    · refine ⟨.L3, .G0, (shift .L3 - z) / g, rfl, ?_⟩
      apply inverse <;> dsimp [shift, supportUpper, g, phi] <;> nlinarith
    have h3' : t - 1 < z := lt_of_not_ge h3
    by_cases h0 : z ≤ 2 * t - 1
    · refine ⟨.L0, .G0, (shift .L0 - z) / g, rfl, ?_⟩
      apply inverse <;> dsimp [shift, supportUpper, g, phi] <;> nlinarith
    have h0' : 2 * t - 1 < z := lt_of_not_ge h0
    refine ⟨.L5, .G1, (shift .L5 - z) / g, rfl, ?_⟩
    apply inverse <;> dsimp [shift, supportUpper, g, T2] <;> nlinarith

/-- One actual legal itinerary realizes every supported scalar, from either guard. -/
theorem lawful_tail (s : Guard) (z : ℝ) (hz : InSupport s z) :
    ∃ (a : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard),
      path 0 = s ∧ x 0 = z ∧
      (∀ p, nextGuard (path p) (a p) = some (path (p + 1))) ∧
      (∀ p, InSupport (path p) (x p)) ∧
      (∀ p, x p = branch (a p) (x (p + 1))) := by
  classical
  let State := {q : Guard × ℝ // InSupport q.1 q.2}
  have progress (q : State) : ∃ (l : Label) (r : State),
      nextGuard q.val.1 l = some r.val.1 ∧ q.val.2 = branch l r.val.2 := by
    obtain ⟨l, e, z', hedge, hsupp, hrec⟩ := inverse_branch q.val.1 q.val.2 q.property
    exact ⟨l, ⟨(e, z'), hsupp⟩, hedge, hrec⟩
  choose label step hedge hrec using progress
  let states : ℕ → State := Nat.rec ⟨(s, z), hz⟩ (fun _ q => step q)
  refine ⟨fun n => label (states n), fun n => (states n).val.2,
    fun n => (states n).val.1, rfl, rfl, ?_, ?_, ?_⟩
  · intro n
    change nextGuard (states n).val.1 (label (states n)) = some (step (states n)).val.1
    exact hedge (states n)
  · intro n
    exact (states n).property
  · intro n
    change (states n).val.2 = branch (label (states n)) (step (states n)).val.2
    exact hrec (states n)

-- The labels are taken from one itinerary, not selected separately for each slot.
private def finiteSegment (a : ℕ → Label) (i : ℕ) : ℕ → List Label
  | 0 => []
  | n + 1 => a i :: finiteSegment a (i + 1) n

private theorem finite_segment_spec
    (a : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard)
    (hedges : ∀ p, nextGuard (path p) (a p) = some (path (p + 1)))
    (hrec : ∀ p, x p = branch (a p) (x (p + 1))) (n i : ℕ) :
    (finiteSegment a i n).length = n ∧
      LegalWord (path i) (path (i + n)) (finiteSegment a i n) ∧
      x i = compose (finiteSegment a i n) (x (i + n)) := by
  induction n generalizing i with
  | zero => simp [finiteSegment, LegalWord, walk, compose]
  | succ n ih =>
    obtain ⟨hlen, hlegal, hvalue⟩ := ih (i + 1)
    have hi : i + 1 + n = i + (n + 1) := by omega
    refine ⟨by simpa [finiteSegment] using congrArg Nat.succ hlen, ?_, ?_⟩
    · simpa [finiteSegment, LegalWord, walk, hedges i, hi] using hlegal
    · calc
        x i = branch (a i) (x (i + 1)) := hrec i
        _ = branch (a i) (compose (finiteSegment a (i + 1) n) (x (i + (n + 1)))) := by
          rw [hvalue, hi]
        _ = compose (finiteSegment a i (n + 1)) (x (i + (n + 1))) := rfl

/-- Truncation at the actual nth coordinate gives arbitrarily close finite-D scalars. -/
theorem finite_approximation (s : Guard) (z : ℝ) (hz : InSupport s z)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (e : Guard) (w : List Label),
      LegalWord s e w ∧ |z - coordinate w 0| < ε := by
  rcases tail_arithmetic with ⟨htq, htp, ht1, hgp, hg1, hphi⟩
  obtain ⟨a, x, path, hpath0, hx0, hedges, hsupp, hrec⟩ := lawful_tail s z hz
  have hlim : Tendsto (fun n : ℕ => phi * g ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hgp.le hg1).const_mul phi
  obtain ⟨n, hn⟩ := (Filter.Tendsto.eventually_lt_const hε hlim).exists
  have segment := finite_segment_spec a x path hedges hrec n 0
  simp only [Nat.zero_add, hpath0, hx0] at segment
  have affine := literal_source_geometry.2.2.2.1 (finiteSegment a 0 n) 0 (x n)
  rw [zero_add, segment.1] at affine
  have hd : z - compose (finiteSegment a 0 n) 0 = (-g) ^ n * x n := by
    have hv := segment.2.2.trans affine
    linarith
  have hu : supportUpper (path n) ≤ phi := by
    cases path n <;> dsimp [supportUpper, phi] <;> linarith
  have hxbound : |x n| ≤ phi := abs_le.mpr
    ⟨by linarith [(hsupp n).1], (hsupp n).2.trans hu⟩
  refine ⟨path n, finiteSegment a 0 n, segment.2.1, ?_⟩
  change |z - compose (finiteSegment a 0 n) 0| < ε
  calc
    |z - compose (finiteSegment a 0 n) 0| = |(-g) ^ n * x n| := congrArg abs hd
    _ = g ^ n * |x n| := by rw [abs_mul, abs_pow, abs_neg, abs_of_pos hgp]
    _ ≤ g ^ n * phi := mul_le_mul_of_nonneg_left hxbound (pow_nonneg hgp.le n)
    _ = phi * g ^ n := mul_comm _ _
    _ < ε := hn

/-- One finite legal tail is chosen in the hull interior, with its entire literal path. -/
theorem finite_tail_interior (s : Guard) (lo hi : ℝ) (hlt : lo < hi)
    (hsupport : ∀ z ∈ Set.Icc lo hi, InSupport s z) :
    ∃ (e : Guard) (w : List Label), LegalWord s e w ∧
      lo < coordinate w 0 ∧ coordinate w 0 < hi ∧
      OperationFiniteSource (address w) ∧
      ∃ path : ℕ → Guard, path 0 = s ∧
        (∀ p, nextGuard (path p) (address w p) = some (path (p + 1))) ∧
        (∀ p, InSupport (path p) (coordinate w p)) ∧
        (∀ p, coordinate w p = branch (address w p) (coordinate w (p + 1))) := by
  have hm : InSupport s ((lo + hi) / 2) :=
    hsupport _ ⟨by linarith, by linarith⟩
  obtain ⟨e, w, hw, herror⟩ :=
    finite_approximation s ((lo + hi) / 2) hm ((hi - lo) / 2) (by linarith)
  have herr := abs_lt.mp herror
  refine ⟨e, w, hw, by linarith [herr.2], by linarith [herr.1], ?_,
    literal_address_path s e w hw⟩
  refine ⟨w.length, ?_⟩
  intro p hp
  simp only [address, List.getElem?_eq_none hp, Option.getD_none]

/-- A legal finite prefix splices the same guard/coordinate tail into an actual source.
The last prefix recurrence and both exact shifted futures are part of the conclusion. -/
theorem prepend_legal_tail
    (s e : Guard) (w : List Label) (hw : LegalWord s e w)
    (a : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard)
    (hpath0 : path 0 = e)
    (hedges : ∀ p, nextGuard (path p) (a p) = some (path (p + 1)))
    (hsupp : ∀ p, InSupport (path p) (x p))
    (hrec : ∀ p, x p = branch (a p) (x (p + 1))) :
    ∃ (b : ℕ → Label) (y : ℕ → ℝ) (q : ℕ → Guard),
      q 0 = s ∧ y 0 = compose w (x 0) ∧
      (∀ p, nextGuard (q p) (b p) = some (q (p + 1))) ∧
      (∀ p, InSupport (q p) (y p)) ∧
      (∀ p, y p = branch (b p) (y (p + 1))) ∧
      (∀ p (hp : p < w.length), b p = w[p]) ∧
      (∀ p, b (w.length + p) = a p) ∧
      (∀ p, y (w.length + p) = x p) := by
  induction w generalizing s with
  | nil =>
    have he : s = e := by simpa [LegalWord, walk] using hw
    refine ⟨a, x, path, hpath0.trans he.symm, rfl, hedges, hsupp, hrec, ?_, ?_, ?_⟩
    · intro p hp
      simp at hp
    · intro p
      simp only [List.length_nil, Nat.zero_add]
    · intro p
      simp only [List.length_nil, Nat.zero_add]
  | cons l w ih =>
    cases hn : nextGuard s l with
    | none => simp [LegalWord, walk, hn] at hw
    | some s' =>
      have hw' : LegalWord s' e w := by simpa [LegalWord, walk, hn] using hw
      obtain ⟨b, y, q, hq0, hy0, hbedges, hbSupp, hbRec, hbPrefix, hbFuture, hyFuture⟩ :=
        ih s' hw'
      refine ⟨(fun p => match p with | 0 => l | n + 1 => b n),
        (fun p => match p with | 0 => compose (l :: w) (x 0) | n + 1 => y n),
        (fun p => match p with | 0 => s | n + 1 => q n),
        rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro p
        cases p with
        | zero => simpa only [hq0] using hn
        | succ p => exact hbedges p
      · intro p
        cases p with
        | zero =>
          exact literal_source_geometry.1 s e (l :: w) (x 0) hw
            (by simpa only [hpath0] using hsupp 0)
        | succ p => exact hbSupp p
      · intro p
        cases p with
        | zero => simpa only [compose, hy0]
        | succ p => exact hbRec p
      · intro p hp
        cases p with
        | zero => rfl
        | succ p =>
          have hp' : p < w.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hp
          simpa only [List.getElem_cons_succ] using hbPrefix p hp'
      · intro p
        simpa only [List.length_cons, Nat.succ_add] using hbFuture p
      · intro p
        simpa only [List.length_cons, Nat.succ_add] using hyFuture p




open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open Filter Topology

/-- Actual cell endpoint ownership, with both outside support endpoints included. -/
def lowerOwned (o : Ownership) (c : Color) : Prop :=
  match c.val with
  | 0 => True | 1 => o 0 = true | 2 => o 1 = true
  | 3 => o 2 = true | 4 => o 3 = true | _ => o 4 = true

def upperOwned (o : Ownership) (c : Color) : Prop :=
  match c.val with
  | 0 => o 0 = false | 1 => o 1 = false | 2 => o 2 = false
  | 3 => o 3 = false | 4 => o 4 = false | _ => True

def FlagInterval (lo hi : ℝ) (left right : Prop) (z : ℝ) : Prop :=
  lo ≤ z ∧ z ≤ hi ∧ (z = lo → left) ∧ (z = hi → right)

private theorem cut_chain :
    cut 0 < cut 1 ∧ cut 1 < cut 2 ∧ cut 2 < cut 3 ∧
    cut 3 < cut 4 ∧ cut 4 < cut 5 ∧ cut 5 < cut 6 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsn := Real.sqrt_nonneg (5 : ℝ)
  have htlo : (3 : ℝ) / 5 < t := by dsimp [t]; nlinarith
  have hthi : t < (2 : ℝ) / 3 := by dsimp [t]; nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [cut, lam, T2, phi, g] <;> linarith

private theorem cut_bounds (c : Color) :
    -1 ≤ cut c.val ∧ cut c.val < cut (c.val + 1) ∧ cut (c.val + 1) ≤ phi := by
  rcases cut_chain with ⟨h01, h12, h23, h34, h45, h56⟩
  fin_cases c <;> norm_num [cut] at *
  all_goals repeat' constructor
  all_goals linarith

/-- Exact cell membership retains the original endpoint ownership. -/
theorem cell_flag_interval (o : Ownership) (c : Color) (u : ℝ) :
    Cell o c u ↔ FlagInterval (cut c.val) (cut (c.val + 1))
      (lowerOwned o c) (upperOwned o c) u := by
  rcases cut_chain with ⟨h01, h12, h23, h34, h45, h56⟩
  fin_cases c <;>
    simp only [Cell, InSupport, supportUpper, FlagInterval, lowerOwned, upperOwned,
      readout, ite_eq_iff]
  all_goals norm_num [cut] at *
  all_goals aesop
  all_goals try linarith
  all_goals try tauto
  all_goals by_cases heq1 : u = -T2 - lam <;> try (simp_all <;> linarith)
  all_goals by_cases heq2 : u = g - 3*lam <;> try (simp_all <;> linarith)
  all_goals by_cases heq3 : u = t - 5*lam <;> try (simp_all <;> linarith)
  all_goals by_cases heq4 : u = 2*t - 7*lam <;> try (simp_all <;> linarith)
  all_goals by_cases heq5 : u = 2*t + lam <;> try (simp_all <;> linarith)
  all_goals simp_all
  all_goals first | (apply lt_of_le_of_ne <;> assumption) | linarith

/-- Closed-budget dilation retains exactly the two original endpoint flags.
The zero-budget branch chooses u=z and does not demand a strict error bound. -/
private theorem flag_dilation (lo hi θ z : ℝ) (left right : Prop)
    (hwidth : lo < hi) (hθ : 0 ≤ θ) :
    (∃ u, FlagInterval lo hi left right u ∧ |z - u| ≤ θ) ↔
      FlagInterval (lo - θ) (hi + θ) left right z := by
  constructor
  · rintro ⟨u, hu, he⟩
    obtain ⟨hel, her⟩ := abs_le.mp he
    refine ⟨by linarith [hu.1], by linarith [hu.2.1], ?_, ?_⟩
    · intro hz
      exact hu.2.2.1 (by linarith [hu.1])
    · intro hz
      exact hu.2.2.2 (by linarith [hu.2.1])
  · intro hz
    by_cases hzero : θ = 0
    · subst θ
      refine ⟨z, ?_, by simp⟩
      simpa only [sub_zero, add_zero] using hz
    have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hzero)
    by_cases hleft : z = lo - θ
    · refine ⟨lo, ⟨le_rfl, hwidth.le, fun _ => hz.2.2.1 hleft, ?_⟩, ?_⟩
      · intro heq
        linarith
      · rw [hleft]
        have : lo - θ - lo = -θ := by ring
        rw [this, abs_neg, abs_of_nonneg hθ]
    by_cases hright : z = hi + θ
    · refine ⟨hi, ⟨hwidth.le, le_rfl, ?_, fun _ => hz.2.2.2 hright⟩, ?_⟩
      · intro heq
        linarith
      · rw [hright]
        have : hi + θ - hi = θ := by ring
        rw [this, abs_of_nonneg hθ]
    have hzlo : lo - θ < z := lt_of_le_of_ne hz.1 (Ne.symm hleft)
    have hzhi : z < hi + θ := lt_of_le_of_ne hz.2.1 hright
    have overlap : max lo (z - θ) < min hi (z + θ) := by
      rw [max_lt_iff, lt_min_iff, lt_min_iff]
      exact ⟨⟨hwidth, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    obtain ⟨u, hlu, huh⟩ := exists_between overlap
    have ulo : lo < u := lt_of_le_of_lt (le_max_left _ _) hlu
    have uhi : u < hi := lt_of_lt_of_le huh (min_le_left _ _)
    have eu : z - θ < u := lt_of_le_of_lt (le_max_right _ _) hlu
    have ue : u < z + θ := lt_of_lt_of_le huh (min_le_right _ _)
    exact ⟨u, ⟨ulo.le, uhi.le, by intro heq; linarith, by intro heq; linarith⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- The actual, supported color-attainable set, not the closed relaxation. -/
def OwnedColor (o : Ownership) (θ : ℝ) (c : Color) (z : ℝ) : Prop :=
  InSupport .G0 z ∧ ∃ u, Cell o c u ∧ |z - u| ≤ θ

theorem owned_color_interval (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (c : Color) (z : ℝ) :
    OwnedColor o θ c z ↔ InSupport .G0 z ∧
      FlagInterval (cut c.val - θ) (cut (c.val + 1) + θ)
        (lowerOwned o c) (upperOwned o c) z := by
  unfold OwnedColor
  simp_rw [cell_flag_interval]
  rw [flag_dilation _ _ _ _ _ _ (cut_bounds c).2.1 hθ]

private theorem clip_fixes (z : ℝ) (hz : InSupport .G0 z) : clip z = z := by
  change -1 ≤ z ∧ z ≤ phi at hz
  simp only [clip, min_eq_right hz.2, max_eq_right hz.1]

private theorem clip_support (z : ℝ) : InSupport .G0 (clip z) := by
  have hphi : (-1 : ℝ) ≤ phi := (cut_bounds 0).1.trans (cut_bounds 0).2.1.le |>.trans (cut_bounds 0).2.2
  exact ⟨le_max_left _ _, max_le hphi (min_le_left _ _)⟩

private theorem clip_error (z e : ℝ) (hz : InSupport .G0 z) :
    |z - clip (z + e)| ≤ |e| := by
  change -1 ≤ z ∧ z ≤ phi at hz
  by_cases hlo : z + e ≤ -1
  · have hhi : z + e ≤ phi := hlo.trans (hz.1.trans hz.2)
    have he : e ≤ 0 := by linarith [hz.1]
    have habs : 0 ≤ z - (-1) := by linarith [hz.1]
    rw [clip, min_eq_right hhi, max_eq_left hlo, abs_of_nonneg habs, abs_of_nonpos he]
    linarith
  by_cases hhi : phi ≤ z + e
  · have hs : (-1 : ℝ) ≤ phi := hz.1.trans hz.2
    have he : 0 ≤ e := by linarith [hz.2]
    have habs : z - phi ≤ 0 := by linarith [hz.2]
    rw [clip, min_eq_left hhi, max_eq_right hs, abs_of_nonpos habs, abs_of_nonneg he]
    linarith
  have hlo' : -1 ≤ z + e := (lt_of_not_ge hlo).le
  have hhi' : z + e ≤ phi := (lt_of_not_ge hhi).le
  rw [clip, min_eq_right hhi', max_eq_right hlo']
  have : z - (z + e) = -e := by ring
  rw [this, abs_neg]

theorem owned_color_error (o : Ownership) (θ : ℝ) (c : Color)
    (z : ℝ) (hz : InSupport .G0 z) :
    OwnedColor o θ c z ↔ ∃ e : ℝ, |e| ≤ θ ∧ observe o z e = c := by
  constructor
  · rintro ⟨_, u, hu, he⟩
    refine ⟨u - z, by simpa only [abs_sub_comm] using he, ?_⟩
    have hsum : z + (u - z) = u := by ring
    simpa only [observe, hsum, clip_fixes u hu.1] using hu.2
  · rintro ⟨e, he, hread⟩
    exact ⟨hz, clip (z + e), ⟨clip_support _, hread⟩, (clip_error z e hz).trans he⟩

private theorem flag_ordConnected (lo hi : ℝ) (left right : Prop) :
    {z | FlagInterval lo hi left right z}.OrdConnected := by
  refine ⟨?_⟩
  intro x hx y hy z hz
  refine ⟨hx.1.trans hz.1, hz.2.trans hy.2.1, ?_, ?_⟩
  · intro hzl
    exact hx.2.2.1 (by linarith [hx.1, hz.1])
  · intro hzh
    exact hy.2.2.2 (by linarith [hy.2.1, hz.2])

theorem owned_color_ordConnected (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ) (c : Color) :
    {z | OwnedColor o θ c z}.OrdConnected := by
  refine ⟨?_⟩
  intro x hx y hy z hz
  obtain ⟨hxs, hxf⟩ := (owned_color_interval o θ hθ c x).mp hx
  obtain ⟨hys, hyf⟩ := (owned_color_interval o θ hθ c y).mp hy
  exact (owned_color_interval o θ hθ c z).mpr
    ⟨⟨hxs.1.trans hz.1, hz.2.trans hys.2⟩,
      (flag_ordConnected _ _ _ _).out hxf hyf hz⟩

private theorem suffix_preimage_ordConnected (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (c : Color) (w : List Label) : {z | OwnedColor o θ c (compose w z)}.OrdConnected := by
  have affine (z : ℝ) : compose w z = compose w 0 + (-g) ^ w.length * z := by
    simpa only [zero_add] using literal_source_geometry.2.2.2.1 w 0 z
  by_cases hsign : 0 ≤ (-g) ^ w.length
  · apply (owned_color_ordConnected o θ hθ c).preimage_mono
    intro x y hxy
    rw [affine x, affine y]
    linarith [mul_le_mul_of_nonneg_left hxy hsign]
  · apply (owned_color_ordConnected o θ hθ c).preimage_anti
    intro x y hxy
    rw [affine x, affine y]
    linarith [mul_le_mul_of_nonpos_left hxy (le_of_not_ge hsign)]

/-- The finite competing-tail set: every stem suffix and both return-color choices.
Only departures r<length are tested. There is no extra terminal color condition. -/
def CompetingT (o : Ownership) (θ : ℝ) (s : Guard)
    (Q V : List Label) (h : List Color) (W : Bool → List Color) : Set ℝ :=
  {z | InSupport s z ∧
    (∀ r (hr : r < h.length), OwnedColor o θ h[r] (compose (Q.drop r) z)) ∧
    (∀ i r (hr : r < (W i).length), OwnedColor o θ (W i)[r] (compose (V.drop r) z))}

theorem competingT_ordConnected (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (s : Guard) (Q V : List Label) (h : List Color) (W : Bool → List Color) :
    (CompetingT o θ s Q V h W).OrdConnected := by
  refine ⟨?_⟩
  intro x hx y hy z hz
  refine ⟨⟨hx.1.1.trans hz.1, hz.2.trans hy.1.2⟩, ?_, ?_⟩
  · intro r hr
    exact (suffix_preimage_ordConnected o θ hθ h[r] (Q.drop r)).out
      (hx.2.1 r hr) (hy.2.1 r hr) hz
  · intro i r hr
    exact (suffix_preimage_ordConnected o θ hθ (W i)[r] (V.drop r)).out
      (hx.2.2 i r hr) (hy.2.2 i r hr) hz

private theorem support_embed (s : Guard) (z : ℝ) (hz : InSupport s z) :
    InSupport .G0 z := by
  have hu : supportUpper s ≤ phi := by cases s <;> dsimp [supportUpper, phi] <;> linarith
  exact ⟨hz.1, hz.2.trans hu⟩

private theorem suffix_supported (s e : Guard) (w : List Label)
    (hw : LegalWord s e w) (z : ℝ) (hz : InSupport e z) (p : ℕ) :
    InSupport .G0 (compose (w.drop p) z) := by
  induction w generalizing s p with
  | nil => simpa [compose] using support_embed e z hz
  | cons l w ih =>
    cases p with
    | zero => exact support_embed s _ (literal_source_geometry.1 s e (l :: w) z hw hz)
    | succ p =>
      cases hn : nextGuard s l with
      | none => simp [LegalWord, walk, hn] at hw
      | some s' =>
        have hw' : LegalWord s' e w := by simpa [LegalWord, walk, hn] using hw
        simpa only [List.drop_succ_cons] using ih s' hw' p

/-- Concrete T is exactly the supported scalar with all actual Q and both W slot tests. -/
theorem competingT_mem_actual (o : Ownership) (θ : ℝ) (s : Guard)
    (Q V : List Label) (h : List Color) (W : Bool → List Color)
    (hQ : LegalWord .G0 s Q) (hV : LegalWord s s V) (z : ℝ) :
    z ∈ CompetingT o θ s Q V h W ↔ InSupport s z ∧
      BlockSupply o θ false Q h z ∧ ∀ i, BlockSupply o θ false V (W i) z := by
  constructor
  · intro hz
    refine ⟨hz.1, ?_, ?_⟩
    · intro r hr
      have hc := hz.2.1 r hr
      simpa only [Bool.false_eq_true, if_false] using (owned_color_error o θ h[r] _ hc.1).mp hc
    · intro i r hr
      have hc := hz.2.2 i r hr
      simpa only [Bool.false_eq_true, if_false] using (owned_color_error o θ (W i)[r] _ hc.1).mp hc
  · rintro ⟨hz, stem, returns⟩
    refine ⟨hz, ?_, ?_⟩
    · intro r hr
      apply (owned_color_error o θ h[r] _ (suffix_supported .G0 s Q hQ z hz r)).mpr
      simpa only [Bool.false_eq_true, if_false] using stem r hr
    · intro i r hr
      apply (owned_color_error o θ (W i)[r] _ (suffix_supported s s V hV z hz r)).mpr
      simpa only [Bool.false_eq_true, if_false] using returns i r hr




open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

/-- The closed relaxation intersects the actual coordinate support. -/
def ClosedExpanded (θ : ℝ) (c : Color) (z : ℝ) : Prop :=
  InSupport .G0 z ∧ cut c.val - θ ≤ z ∧ z ≤ cut (c.val + 1) + θ

private theorem expanded_distance_formula (θ : ℝ) (hθ : 0 ≤ θ) (c : Color) (z : ℝ) :
    ClosedExpanded θ c z ↔ InSupport .G0 z ∧
      max (cut c.val-z) (max 0 (z-cut (c.val+1))) ≤ θ := by
  simp only [ClosedExpanded,max_le_iff]
  constructor
  · rintro ⟨hs,hlo,hhi⟩
    exact ⟨hs,by linarith,hθ,by linarith⟩
  · rintro ⟨hs,hlo,_,hhi⟩
    exact ⟨hs,by linarith,by linarith⟩

/-- Two actual numeric endpoint costs at every observed departure suffix. -/
def EndpointCertificate (θ : ℝ) (lo hi : ℝ) (w : List Label) (cs : List Color) : Prop :=
  ∀ r (hr : r < cs.length),
    (InSupport .G0 (compose (w.drop r) lo) ∧
      max (cut cs[r].val-compose (w.drop r) lo)
        (max 0 (compose (w.drop r) lo-cut (cs[r].val+1))) ≤ θ) ∧
    (InSupport .G0 (compose (w.drop r) hi) ∧
      max (cut cs[r].val-compose (w.drop r) hi)
        (max 0 (compose (w.drop r) hi-cut (cs[r].val+1))) ≤ θ)

private theorem literal_slope_ne_zero (w : List Label) : (-g) ^ w.length ≠ 0 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsn := Real.sqrt_nonneg (5 : ℝ)
  have hgp : 0 < g := by dsimp [g, t]; nlinarith
  exact pow_ne_zero _ (neg_ne_zero.mpr (ne_of_gt hgp))

private theorem compose_strict_inside (w : List Label) (lo hi x left right : ℝ)
    (hxlo : lo < x) (hxhi : x < hi)
    (hlo : left ≤ compose w lo ∧ compose w lo ≤ right)
    (hhi : left ≤ compose w hi ∧ compose w hi ≤ right) :
    left < compose w x ∧ compose w x < right := by
  have affine (z : ℝ) : compose w z = compose w 0 + (-g) ^ w.length * z := by
    simpa only [zero_add] using literal_source_geometry.2.2.2.1 w 0 z
  have hne := literal_slope_ne_zero w
  by_cases hpos : 0 < (-g) ^ w.length
  · have hxl : compose w lo < compose w x := by
      rw [affine lo, affine x]
      nlinarith [mul_pos hpos (sub_pos.mpr hxlo)]
    have hxh : compose w x < compose w hi := by
      rw [affine x, affine hi]
      nlinarith [mul_pos hpos (sub_pos.mpr hxhi)]
    exact ⟨lt_of_le_of_lt hlo.1 hxl, lt_of_lt_of_le hxh hhi.2⟩
  · have hneg : (-g) ^ w.length < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hne
    have hxl : compose w hi < compose w x := by
      rw [affine hi, affine x]
      nlinarith [mul_neg_of_neg_of_pos hneg (sub_pos.mpr hxhi)]
    have hxh : compose w x < compose w lo := by
      rw [affine x, affine lo]
      nlinarith [mul_neg_of_neg_of_pos hneg (sub_pos.mpr hxlo)]
    exact ⟨lt_of_le_of_lt hhi.1 hxl, lt_of_lt_of_le hxh hlo.2⟩

/-- Finite endpoint data gives actual readout witnesses at every departure, at theta itself. -/
theorem certificate_actual_slots (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (lo hi : ℝ) (w : List Label) (cs : List Color)
    (cert : EndpointCertificate θ lo hi w cs)
    (x : ℝ) (hxlo : lo < x) (hxhi : x < hi) :
    BlockSupply o θ false w cs x := by
  intro r hr
  obtain ⟨hleft, hright⟩ := cert r hr
  have hl := (expanded_distance_formula θ hθ cs[r] _).mpr hleft
  have hh := (expanded_distance_formula θ hθ cs[r] _).mpr hright
  have supported := compose_strict_inside (w.drop r) lo hi x (-1) phi hxlo hxhi hl.1 hh.1
  have expanded := compose_strict_inside (w.drop r) lo hi x
    (cut cs[r].val - θ) (cut (cs[r].val + 1) + θ) hxlo hxhi hl.2 hh.2
  have hs : InSupport .G0 (compose (w.drop r) x) := ⟨supported.1.le, supported.2.le⟩
  have actual : OwnedColor o θ cs[r] (compose (w.drop r) x) :=
    (owned_color_interval o θ hθ cs[r] _).mpr
      ⟨hs, expanded.1.le, expanded.2.le,
        by intro heq; linarith [expanded.1], by intro heq; linarith [expanded.2]⟩
  simpa only [Bool.false_eq_true, if_false] using
    (owned_color_error o θ cs[r] _ hs).mp actual

private theorem block_supply_append (o : Ownership) (θ : ℝ)
    (u v : List Label) (cu cv : List Color) (hlen : u.length = cu.length) (z : ℝ)
    (hu : BlockSupply o θ false u cu (compose v z))
    (hv : BlockSupply o θ false v cv z) :
    BlockSupply o θ false (u ++ v) (cu ++ cv) z := by
  intro r hr
  by_cases hp : r < cu.length
  · have hp' : r ≤ u.length := by omega
    simpa only [List.getElem_append_left hp, List.drop_append_of_le_length hp',
      literal_source_geometry.2.2.2.2] using hu r hp
  · have hle : u.length ≤ r := by omega
    have hr' : r - cu.length < cv.length := by
      simp only [List.length_append] at hr
      omega
    have value := hv (r - cu.length) hr'
    simpa only [List.getElem_append_right (le_of_not_gt hp), List.drop_append,
      List.drop_eq_nil_of_le hle, List.nil_append, hlen] using value

def choiceBlocks {α : Type} (words : Bool → List α) : List Bool → List α
  | [] => []
  | i :: zs => words i ++ choiceBlocks words zs

private theorem choice_lengths (R : Bool → List Label) (W : Bool → List Color)
    (hlen : ∀ i, (R i).length = (W i).length) (zs : List Bool) :
    (choiceBlocks R zs).length = (choiceBlocks W zs).length := by
  induction zs with
  | nil => rfl
  | cons i zs ih => simp only [choiceBlocks, List.length_append, hlen, ih]

private theorem legal_append (s e q : Guard) (u v : List Label)
    (hu : LegalWord s e u) (hv : LegalWord e q v) : LegalWord s q (u ++ v) := by
  induction u generalizing s with
  | nil =>
    have hse : s = e := by simpa [LegalWord, walk] using hu
    simpa [hse] using hv
  | cons l u ih =>
    cases hn : nextGuard s l with
    | none => simp [LegalWord, walk, hn] at hu
    | some s' =>
      have hu' : LegalWord s' e u := by simpa [LegalWord, walk, hn] using hu
      simpa [LegalWord, walk, hn] using ih s' hu'

private theorem choices_legal (s : Guard) (R : Bool → List Label)
    (hR : ∀ i, LegalWord s s (R i)) (zs : List Bool) :
    LegalWord s s (choiceBlocks R zs) := by
  induction zs with
  | nil => rfl
  | cons i zs ih => exact legal_append s s s (R i) _ (hR i) ih

private theorem choices_interior (R : Bool → List Label) (lo hi : ℝ)
    (invariant : ∀ i z, lo ≤ z → z ≤ hi → lo ≤ compose (R i) z ∧ compose (R i) z ≤ hi)
    (x : ℝ) (hxlo : lo < x) (hxhi : x < hi) (zs : List Bool) :
    lo < compose (choiceBlocks R zs) x ∧ compose (choiceBlocks R zs) x < hi := by
  induction zs with
  | nil => exact ⟨hxlo, hxhi⟩
  | cons i zs ih =>
    have width : lo ≤ hi := (hxlo.trans hxhi).le
    have h := compose_strict_inside (R i) lo hi (compose (choiceBlocks R zs) x) lo hi
      ih.1 ih.2 (invariant i lo le_rfl width) (invariant i hi width le_rfl)
    simpa only [choiceBlocks, literal_source_geometry.2.2.2.2] using h

private theorem choices_actual_slots (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (lo hi : ℝ) (R : Bool → List Label) (W : Bool → List Color)
    (hlen : ∀ i, (R i).length = (W i).length)
    (invariant : ∀ i z, lo ≤ z → z ≤ hi → lo ≤ compose (R i) z ∧ compose (R i) z ≤ hi)
    (cert : ∀ i, EndpointCertificate θ lo hi (R i) (W i))
    (x : ℝ) (hxlo : lo < x) (hxhi : x < hi) (zs : List Bool) :
    BlockSupply o θ false (choiceBlocks R zs) (choiceBlocks W zs) x := by
  induction zs with
  | nil => intro r hr; simp [choiceBlocks] at hr
  | cons i zs ih =>
    have hinside := choices_interior R lo hi invariant x hxlo hxhi zs
    exact block_supply_append o θ (R i) _ (W i) _ (hlen i) x
      (certificate_actual_slots o θ hθ lo hi (R i) (W i) (cert i) _ hinside.1 hinside.2) ih

/-- One finite history followed by the literal zero-error future of the same fixed tail. -/
noncomputable def recordWithTail (o : Ownership) (cs : List Color) (w : List Label)
    (p : ℕ) : Color :=
  if hp : p < cs.length then cs[p] else observe o (coordinate w (p - cs.length)) 0

private theorem actual_prefix_record (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (s e : Guard) (A : List Label) (cs : List Color) (hlen : A.length = cs.length)
    (hA : LegalWord .G0 s A) (w : List Label) (hw : LegalWord s e w)
    (supply : BlockSupply o θ false A cs (coordinate w 0)) :
    OperationRecord o θ .closed (address (A ++ w)) (recordWithTail o cs w) ∧
      OperationFiniteSource (address (A ++ w)) := by
  classical
  have legal := legal_append .G0 s e A w hA hw
  obtain ⟨path, hp0, hedge, hsupp, hrec⟩ := literal_address_path .G0 e (A ++ w) legal
  have supplied (j : Fin cs.length) : ∃ error : ℝ,
      |error| ≤ θ ∧ observe o (compose (A.drop j.val) (coordinate w 0)) error = cs[j.val] := by
    simpa only [Bool.false_eq_true, if_false] using supply j.val j.isLt
  choose error hbound hcolor using supplied
  let errors : ℕ → ℝ := fun p => if hp : p < cs.length then error ⟨p, hp⟩ else 0
  have past (p : ℕ) (hp : p < cs.length) :
      coordinate (A ++ w) p = compose (A.drop p) (coordinate w 0) := by
    have hp' : p ≤ A.length := by omega
    simp only [coordinate, List.drop_append_of_le_length hp',
      literal_source_geometry.2.2.2.2, List.drop_zero]
  have future (p : ℕ) (hp : cs.length ≤ p) :
      coordinate (A ++ w) p = coordinate w (p - cs.length) := by
    have hp' : A.length ≤ p := by omega
    simp only [coordinate, List.drop_append, List.drop_eq_nil_of_le hp', List.nil_append, hlen]
  refine ⟨⟨coordinate (A ++ w), ⟨path, hp0, hedge, hsupp, hrec⟩, errors, ?_, ?_⟩, ?_⟩
  · intro p
    by_cases hp : p < cs.length
    · simpa only [errors, dif_pos hp] using hbound ⟨p, hp⟩
    · simpa only [errors, dif_neg hp, abs_zero] using hθ
  · intro p
    by_cases hp : p < cs.length
    · simpa only [recordWithTail, dif_pos hp, errors, past p hp] using hcolor ⟨p, hp⟩
    · simp only [recordWithTail, dif_neg hp, errors, future p (le_of_not_gt hp)]
  · refine ⟨(A ++ w).length, ?_⟩
    intro p hp
    simp only [address, List.getElem?_eq_none hp, Option.getD_none]

/-- The finite endpoint certificate constructs one fixed finite actual tail
serving every finite choice history. It does not assume any record family. -/
theorem fixed_finite_tail_all_histories
    (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (s : Guard) (P : List Label) (h : List Color) (hP : LegalWord .G0 s P)
    (hPlen : P.length = h.length)
    (R : Bool → List Label) (W : Bool → List Color)
    (hR : ∀ i, LegalWord s s (R i)) (hlen : ∀ i, (R i).length = (W i).length)
    (lo hi : ℝ) (hwidth : lo < hi)
    (hsupport : ∀ z ∈ Set.Icc lo hi, InSupport s z)
    (invariant : ∀ i z, lo ≤ z → z ≤ hi → lo ≤ compose (R i) z ∧ compose (R i) z ≤ hi)
    (stemCert : EndpointCertificate θ lo hi P h)
    (returnCert : ∀ i, EndpointCertificate θ lo hi (R i) (W i)) :
    ∃ (e : Guard) (w : List Label), LegalWord s e w ∧
      lo < coordinate w 0 ∧ coordinate w 0 < hi ∧
      ∀ zs : List Bool,
        OperationRecord o θ .closed (address ((P ++ choiceBlocks R zs) ++ w))
          (recordWithTail o (h ++ choiceBlocks W zs) w) ∧
        OperationFiniteSource (address ((P ++ choiceBlocks R zs) ++ w)) ∧
        ∀ p, recordWithTail o (h ++ choiceBlocks W zs) w
          ((h ++ choiceBlocks W zs).length + p) = observe o (coordinate w p) 0 := by
  obtain ⟨e, w, hw, hxlo, hxhi, hfinite, hpath⟩ :=
    finite_tail_interior s lo hi hwidth hsupport
  refine ⟨e, w, hw, hxlo, hxhi, ?_⟩
  intro zs
  have inside := choices_interior R lo hi invariant (coordinate w 0) hxlo hxhi zs
  have stemSupply := certificate_actual_slots o θ hθ lo hi P h stemCert _ inside.1 inside.2
  have returnSupply := choices_actual_slots o θ hθ lo hi R W hlen invariant returnCert
    (coordinate w 0) hxlo hxhi zs
  have allSupply := block_supply_append o θ P (choiceBlocks R zs) h (choiceBlocks W zs)
    hPlen (coordinate w 0) stemSupply returnSupply
  have allLegal := legal_append .G0 s s P (choiceBlocks R zs) hP (choices_legal s R hR zs)
  have allLength : (P ++ choiceBlocks R zs).length = (h ++ choiceBlocks W zs).length := by
    simp only [List.length_append, hPlen, choice_lengths R W hlen zs]
  obtain ⟨actual, finite⟩ := actual_prefix_record o θ hθ s e (P ++ choiceBlocks R zs)
    (h ++ choiceBlocks W zs) allLength allLegal w hw allSupply
  refine ⟨actual, finite, ?_⟩
  intro p
  have hp : ¬ (h ++ choiceBlocks W zs).length + p < (h ++ choiceBlocks W zs).length := by omega
  simp only [recordWithTail, dif_neg hp, Nat.add_sub_cancel_left]




private theorem prefix_coordinates (A : List Label) (beta : ℕ → Label) (X : ℕ → ℝ)
    (z : ℝ) (prefixLabels : ∀ p (hp : p < A.length), beta p = A[p])
    (recurrence : ∀ p, X p = branch (beta p) (X (p+1)))
    (terminal : X A.length = z) :
    ∀ p, p ≤ A.length → X p = compose (A.drop p) z := by
  induction A generalizing beta X with
  | nil =>
    intro p hp
    have hp0 : p = 0 := by simpa using hp
    subst p
    simpa only [List.length_nil, List.drop_nil, compose] using terminal
  | cons l A ih =>
    have hpre : ∀ p (hp : p < A.length), beta (p+1) = A[p] := by
      intro p hp
      have hh := prefixLabels (p+1) (by simp; omega)
      change beta (p+1) = A[p] at hh
      exact hh
    have hend : X (A.length+1) = z := by simpa only [List.length_cons] using terminal
    have ht := ih (fun p => beta (p+1)) (fun p => X (p+1)) hpre
      (fun p => by simpa only [Nat.add_assoc] using recurrence (p+1)) hend
    intro p hp
    cases p with
    | zero =>
      rw [recurrence 0, prefixLabels 0 (by simp), ht 0 (Nat.zero_le _)]
      rfl
    | succ p =>
      simpa only [List.drop_succ_cons, Nat.succ_eq_add_one] using ht p (by simp at hp; omega)

noncomputable def recordWithOmegaTail (o : Ownership) (cs : List Color)
    (x : ℕ → ℝ) (p : ℕ) : Color :=
  if hp : p < cs.length then cs[p] else observe o (x (p-cs.length)) 0

private theorem actual_omega_prefix_record (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (s : Guard) (A : List Label) (cs : List Color) (hlen : A.length = cs.length)
    (hA : LegalWord .G0 s A)
    (tail : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard)
    (hp0 : path 0 = s)
    (hedge : ∀ p, nextGuard (path p) (tail p) = some (path (p+1)))
    (hsupp : ∀ p, InSupport (path p) (x p))
    (hrec : ∀ p, x p = branch (tail p) (x (p+1)))
    (supply : BlockSupply o θ false A cs (x 0)) :
    ∃ beta X, OperationOmega beta X ∧
      (∀ p (hp : p < A.length), beta p = A[p]) ∧
      (∀ p, beta (A.length+p) = tail p) ∧
      (∀ p, X (A.length+p) = x p) ∧
      OperationRecord o θ .closed beta (recordWithOmegaTail o cs x) := by
  classical
  obtain ⟨beta,X,q,hq0,hX0,he,hs,hr,pre,future,coords⟩ :=
    prepend_legal_tail .G0 s A hA tail x path hp0 hedge hsupp hrec
  have legal : OperationOmega beta X := ⟨q,hq0,he,hs,hr⟩
  have terminal : X A.length = x 0 := by simpa only [Nat.add_zero] using coords 0
  have past := prefix_coordinates A beta X (x 0) pre hr terminal
  have supplied (j : Fin cs.length) : ∃ e : ℝ,
      |e| ≤ θ ∧ observe o (X j.val) e = cs[j.val] := by
    rw [past j.val (by omega)]
    simpa only [Bool.false_eq_true, if_false] using supply j.val j.isLt
  choose error bound color using supplied
  let errors : ℕ → ℝ := fun p => if hp : p < cs.length then error ⟨p,hp⟩ else 0
  refine ⟨beta,X,legal,pre,future,coords,X,legal,errors,?_,?_⟩
  · intro p
    by_cases hp : p < cs.length
    · simpa only [errors,dif_pos hp] using bound ⟨p,hp⟩
    · simpa only [errors,dif_neg hp,abs_zero] using hθ
  · intro p
    by_cases hp : p < cs.length
    · simpa only [recordWithOmegaTail,errors,dif_pos hp] using color ⟨p,hp⟩
    · have hle : A.length ≤ p := by omega
      have hx : X p = x (p-cs.length) := by
        have hh := coords (p-A.length)
        rw [Nat.add_sub_of_le hle] at hh
        simpa only [hlen] using hh
      simp only [recordWithOmegaTail,errors,dif_neg hp,hx]

private theorem compose_identical_choices (V : List Label) (zs : List Bool) (z : ℝ) :
    compose (choiceBlocks (fun _ => V) zs) z = (compose V)^[zs.length] z := by
  induction zs with
  | nil => rfl
  | cons i zs ih =>
    simp only [choiceBlocks,literal_source_geometry.2.2.2.2,List.length_cons,
      Function.iterate_succ_apply',ih]

private theorem identical_choices_slots (o : Ownership) (θ : ℝ) (s : Guard)
    (Q V : List Label) (h : List Color) (W : Bool → List Color)
    (hQ : LegalWord .G0 s Q) (hV : LegalWord s s V)
    (hlen : ∀ i, V.length = (W i).length) (z : ℝ)
    (orbit : ∀ n, (compose V)^[n] z ∈ CompetingT o θ s Q V h W)
    (zs : List Bool) :
    BlockSupply o θ false (choiceBlocks (fun _ => V) zs) (choiceBlocks W zs) z := by
  induction zs with
  | nil => intro r hr; simp [choiceBlocks] at hr
  | cons i zs ih =>
    have ht := (competingT_mem_actual o θ s Q V h W hQ hV _).mp (orbit zs.length)
    have hv : BlockSupply o θ false V (W i)
        (compose (choiceBlocks (fun _ => V) zs) z) := by
      simpa only [compose_identical_choices] using ht.2.2 i
    exact block_supply_append o θ V _ (W i) _ (hlen i) z hv ih

private theorem block_supply_split (o : Ownership) (θ : ℝ)
    (A B : List Label) (h d : List Color) (hlen : A.length = h.length) (z : ℝ)
    (supply : BlockSupply o θ false (A++B) (h++d) z) :
    BlockSupply o θ false A h (compose B z) ∧ BlockSupply o θ false B d z := by
  constructor
  · intro r hr
    have hrall : r < (h++d).length := by simp; omega
    have hs := supply r hrall
    have hrA : r ≤ A.length := by omega
    simpa only [List.getElem_append_left hr,List.drop_append_of_le_length hrA,
      literal_source_geometry.2.2.2.2] using hs
  · intro r hr
    have hrall : h.length+r < (h++d).length := by simp; omega
    have hs := supply (h.length+r) hrall
    have hrge : A.length ≤ h.length+r := by omega
    have hcolor : (h++d)[h.length+r] = d[r] := by
      simpa only [Nat.add_sub_cancel_left] using List.getElem_append_right (by omega : h.length ≤ h.length+r)
    rw [hcolor] at hs
    rw [List.drop_append,List.drop_eq_nil_of_le hrge,List.nil_append] at hs
    simpa only [← hlen,Nat.add_sub_cancel_left] using hs

private theorem competingT_orbit_iff_all_histories (o : Ownership) (θ : ℝ) (s : Guard)
    (Q V : List Label) (h : List Color) (W : Bool → List Color)
    (hQ : LegalWord .G0 s Q) (hV : LegalWord s s V)
    (hQlen : Q.length = h.length) (hlen : ∀ i, V.length = (W i).length) (z : ℝ) :
    (∀ n, (compose V)^[n] z ∈ CompetingT o θ s Q V h W) ↔
      InSupport s z ∧ ∀ zs : List Bool,
        BlockSupply o θ false (Q++choiceBlocks (fun _ => V) zs) (h++choiceBlocks W zs) z := by
  constructor
  · intro orbit
    have hz : z ∈ CompetingT o θ s Q V h W := by simpa using orbit 0
    refine ⟨hz.1,?_⟩
    intro zs
    have stem := ((competingT_mem_actual o θ s Q V h W hQ hV _).mp (orbit zs.length)).2.1
    have stem' : BlockSupply o θ false Q h (compose (choiceBlocks (fun _ => V) zs) z) := by
      simpa only [compose_identical_choices] using stem
    exact block_supply_append o θ Q _ h _ hQlen z stem'
      (identical_choices_slots o θ s Q V h W hQ hV hlen z orbit zs)
  · rintro ⟨hz,supplies⟩
    have supported (n : ℕ) : InSupport s ((compose V)^[n] z) := by
      induction n with
      | zero => exact hz
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact literal_source_geometry.1 s s V _ hV ih
    intro n
    let zs : List Bool := List.replicate n false
    have hzs : zs.length = n := by simp [zs]
    have hs := (block_supply_split o θ Q _ h _ hQlen z (supplies zs)).1
    have hs' : BlockSupply o θ false Q h ((compose V)^[n] z) := by
      simpa only [compose_identical_choices,hzs] using hs
    apply (competingT_mem_actual o θ s Q V h W hQ hV _).mpr
    refine ⟨supported n,hs',?_⟩
    intro i
    have hs := (block_supply_split o θ Q _ h _ hQlen z (supplies (i::zs))).2
    change BlockSupply o θ false (V++choiceBlocks (fun _ => V) zs) (W i++choiceBlocks W zs) z at hs
    have hv := (block_supply_split o θ V _ (W i) _ (hlen i) z hs).1
    simpa only [compose_identical_choices,hzs] using hv

/-- One lawful competing tail supplies every finite synchronized color history. -/
theorem fixed_omega_tail_all_histories
    (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ) (s : Guard)
    (Q V : List Label) (h : List Color) (W : Bool → List Color)
    (hQ : LegalWord .G0 s Q) (hV : LegalWord s s V)
    (hQlen : Q.length = h.length) (hlen : ∀ i, V.length = (W i).length)
    (a y : ℝ) (ha : -1 < a) (ha1 : a < 1) (hane : a ≠ 0)
    (hslope : a = (-g)^V.length) (hfixed : compose V y = y)
    (hfeasible : if 0 < a then
      (CompetingT o θ s Q V h W).Nonempty ∧ y ∈ closure (CompetingT o θ s Q V h W)
      else y ∈ CompetingT o θ s Q V h W) :
    ∃ (tail : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard),
      path 0 = s ∧
      (∀ p, nextGuard (path p) (tail p) = some (path (p+1))) ∧
      (∀ p, InSupport (path p) (x p)) ∧
      (∀ p, x p = branch (tail p) (x (p+1))) ∧
      (∀ n, (compose V)^[n] (x 0) ∈ CompetingT o θ s Q V h W) ∧
      ∀ zs : List Bool, ∃ beta X, OperationOmega beta X ∧
        (∀ p (hp : p < (Q ++ choiceBlocks (fun _ => V) zs).length),
          beta p = (Q ++ choiceBlocks (fun _ => V) zs)[p]) ∧
        (∀ p, beta ((Q ++ choiceBlocks (fun _ => V) zs).length+p) = tail p) ∧
        (∀ p, X ((Q ++ choiceBlocks (fun _ => V) zs).length+p) = x p) ∧
        OperationRecord o θ .closed beta (recordWithOmegaTail o (h ++ choiceBlocks W zs) x) := by
  have hF : compose V = (fun z : ℝ => y+a*(z-y)) := by
    funext z
    have affine := literal_source_geometry.2.2.2.1 V y (z-y)
    have hsum : y+(z-y) = z := by ring
    simpa only [hsum,hfixed,← hslope] using affine
  obtain ⟨z,hzOrbit⟩ := (competing_tail_orbit_criterion _
    (competingT_ordConnected o θ hθ s Q V h W) a y ha ha1 hane).2.mpr hfeasible
  have orbit : ∀ n, (compose V)^[n] z ∈ CompetingT o θ s Q V h W := by
    intro n
    rw [hF]
    exact hzOrbit n
  have hzT : z ∈ CompetingT o θ s Q V h W := by simpa using orbit 0
  obtain ⟨tail,x,path,hp0,hx0,he,hs,hr⟩ := lawful_tail s z hzT.1
  refine ⟨tail,x,path,hp0,he,hs,hr,by simpa only [hx0] using orbit,?_⟩
  intro zs
  have supply := ((competingT_orbit_iff_all_histories o θ s Q V h W hQ hV hQlen hlen z).mp orbit).2 zs
  have supply' : BlockSupply o θ false (Q++choiceBlocks (fun _ => V) zs) (h++choiceBlocks W zs) (x 0) := by
    simpa only [hx0] using supply
  have hA := legal_append .G0 s s Q _ hQ (choices_legal s (fun _ => V) (fun _ => hV) zs)
  have hAlen : (Q ++ choiceBlocks (fun _ => V) zs).length = (h ++ choiceBlocks W zs).length := by
    simp only [List.length_append,hQlen,choice_lengths (fun _ => V) W hlen zs]
  exact actual_omega_prefix_record o θ hθ s _ _ hAlen hA tail x path hp0 he hs hr supply'



open D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

private theorem uniform_choice_length {A : Type} (R : Bool → List A)
    (L : ℕ) (hlen : ∀ i, (R i).length = L) (zs : List Bool) :
    (choiceBlocks R zs).length = zs.length * L := by
  induction zs with
  | nil => simp only [choiceBlocks,List.length_nil,Nat.zero_mul]
  | cons i zs ih => simp only [choiceBlocks,List.length_append,hlen,ih,List.length_cons,Nat.succ_mul]; omega

private theorem uniform_choice_injective (R : Bool → List Label) (L : ℕ)
    (hlen : ∀ i, (R i).length = L) (hne : R false ≠ R true)
    (zs ys : List Bool) (hsize : zs.length = ys.length)
    (heq : choiceBlocks R zs = choiceBlocks R ys) : zs = ys := by
  induction zs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons j ys => simp at hsize
  | cons i zs ih =>
    cases ys with
    | nil => simp at hsize
    | cons j ys =>
      have head (i : Bool) (rs : List Bool) :
          (choiceBlocks R (i :: rs)).take L = R i := by
        change (R i ++ choiceBlocks R rs).take L = R i
        rw [← hlen i]
        exact List.take_left
      have hij : R i = R j := by
        calc R i = (choiceBlocks R (i :: zs)).take L := (head i zs).symm
             _ = (choiceBlocks R (j :: ys)).take L := congrArg (List.take L) heq
             _ = R j := head j ys
      have hchoice : i = j := by
        cases i <;> cases j
        · rfl
        · exact False.elim (hne hij)
        · exact False.elim (hne hij.symm)
        · rfl
      subst j
      have tail : choiceBlocks R zs = choiceBlocks R ys :=
        List.append_cancel_left (by simpa only [choiceBlocks] using heq)
      exact congrArg (List.cons i) (ih ys (by simpa only [List.length_cons,Nat.succ_inj] using hsize) tail)

def synchronousPrefix {A : Type} (P : List A) (R : Bool → List A)
    {n : ℕ} (z : Fin n → Bool) : List A := P ++ choiceBlocks R (List.ofFn z)

private theorem synchronous_length {A : Type} (P : List A) (R : Bool → List A)
    (L : ℕ) (hlen : ∀ i, (R i).length = L) (n : ℕ) (z : Fin n → Bool) :
    (synchronousPrefix P R z).length = P.length + n*L := by
  simp only [synchronousPrefix,List.length_append,uniform_choice_length R L hlen,List.length_ofFn]

private theorem address_prefix (A w : List Label) (p : ℕ) (hp : p < A.length) :
    address (A ++ w) p = A[p] := by
  have htotal : p < (A ++ w).length := by simp; omega
  simp only [address,List.getElem?_eq_getElem htotal,Option.getD_some,List.getElem_append_left hp]

private theorem synchronous_address_injective (P : List Label) (R : Bool → List Label)
    (L : ℕ) (hlen : ∀ i, (R i).length = L) (hne : R false ≠ R true)
    (w : List Label) (n : ℕ) :
    Function.Injective (fun z : Fin n → Bool => address (synchronousPrefix P R z ++ w)) := by
  intro z z' heq
  have hsize : (synchronousPrefix P R z).length = (synchronousPrefix P R z').length := by
    rw [synchronous_length P R L hlen n z,synchronous_length P R L hlen n z']
  have hpref : synchronousPrefix P R z = synchronousPrefix P R z' := by
    apply List.ext_getElem hsize
    intro p hp hp'
    calc (synchronousPrefix P R z)[p] = address (synchronousPrefix P R z ++ w) p :=
           (address_prefix _ w p hp).symm
         _ = address (synchronousPrefix P R z' ++ w) p := congrFun heq p
         _ = (synchronousPrefix P R z')[p] := address_prefix _ w p hp'
  have blocks : choiceBlocks R (List.ofFn z) = choiceBlocks R (List.ofFn z') :=
    List.append_cancel_left hpref
  apply List.ofFn_injective
  exact uniform_choice_injective R L hlen hne _ _ (by simp) blocks

private theorem zero_record (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (e : Guard) (w : List Label) (hw : LegalWord .G0 e w) :
    OperationRecord o θ .closed (address w) (fun p => observe o (coordinate w p) 0) ∧
      OperationFiniteSource (address w) := by
  obtain ⟨path,hp0,he,hs,hr⟩ := literal_address_path .G0 e w hw
  refine ⟨⟨coordinate w,⟨path,hp0,he,hs,hr⟩,(fun _ => 0),?_,?_⟩,w.length,?_⟩
  · intro p
    simpa only [abs_zero] using hθ
  · intro p
    rfl
  · intro p hp
    simp only [address,List.getElem?_eq_none hp,Option.getD_none]

/-- Actual synchronized sources give the original arbitrary common-stem factor.
The finite hull and endpoint data are numerical inputs, not record or injection inputs. -/
theorem original_synchronous_common_stem {Configuration : Type*}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (s1 s2 : Guard) (P Q : List Label) (h : List Color)
    (hP : LegalWord .G0 s1 P) (hQ : LegalWord .G0 s2 Q)
    (hPlen : P.length = h.length) (hQlen : Q.length = h.length)
    (U : Bool → List Label) (V : List Label) (W : Bool → List Color)
    (L : ℕ) (hL : 0 < L) (hU : ∀ i, LegalWord s1 s1 (U i))
    (hV : LegalWord s2 s2 V) (hUlen : ∀ i, (U i).length = L)
    (hVlen : V.length = L) (hUWlen : ∀ i, (U i).length = (W i).length)
    (differentReturns : U false ≠ U true)
    (lo hi : ℝ) (hwidth : lo < hi)
    (hsupport : ∀ z ∈ Set.Icc lo hi, InSupport s1 z)
    (invariant : ∀ i z, lo ≤ z → z ≤ hi → lo ≤ compose (U i) z ∧ compose (U i) z ≤ hi)
    (stemCert : EndpointCertificate θ lo hi P h)
    (returnCert : ∀ i, EndpointCertificate θ lo hi (U i) (W i))
    (a y : ℝ) (ha : -1 < a) (ha1 : a < 1) (hane : a ≠ 0)
    (hslope : a = (-g)^V.length) (hfixed : compose V y = y)
    (hfeasible : if 0 < a then
      (CompetingT o θ s2 Q V h W).Nonempty ∧ y ∈ closure (CompetingT o θ s2 Q V h W)
      else y ∈ CompetingT o θ s2 Q V h W)
    (k : ℕ) (hk : k < P.length)
    (sameStem : ∀ p (hp : p < k), P[p] = Q[p]'(by omega))
    (differentStem : P[k] ≠ Q[k]'(by omega))
    (safety : ∀ alpha r, OperationRecord o θ .closed alpha r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = alpha p)
    (liveness : ∀ alpha r, OperationRecord o θ .closed alpha r → OperationFiniteSource alpha → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (postprocessing : ∀ alpha r, OperationRecord o θ .closed alpha r →
      ∀ (c d : Configuration) (q : ℕ) (out batch : List Label)
      (f : Color → Option (Configuration × List Label)),
      Run action (full r) ⟨initialConfiguration,0,[]⟩ ⟨c,q,out⟩ →
      action c = .acquire f → f (r q) = some (d,batch) →
      ∃ t, Drain action ⟨d,q+1,out++batch⟩ t) :
    ∃ (e : Guard) (w : List Label) (eta : ℕ → Label) (x : ℕ → ℝ),
      LegalWord s1 e w ∧ lo < coordinate w 0 ∧ coordinate w 0 < hi ∧
      ∀ n : ℕ, ∃ (beta : (Fin n → Bool) → ℕ → Label)
        (cuts : (Fin n → Bool) → Frame Configuration Label) (states : Finset Configuration),
        (∀ (z : Fin n → Bool), OperationRecord o θ .closed
          (address (synchronousPrefix P U z ++ w))
          (recordWithTail o (synchronousPrefix h W z) w) ∧
          OperationFiniteSource (address (synchronousPrefix P U z ++ w))) ∧
        (∀ (z : Fin n → Bool), OperationRecord o θ .closed (beta z)
          (recordWithOmegaTail o (synchronousPrefix h W z) x)) ∧
        (∀ (z : Fin n → Bool) p (hp : p < (synchronousPrefix Q (fun _ => V) z).length),
          beta z p = (synchronousPrefix Q (fun _ => V) z)[p]) ∧
        (∀ (z : Fin n → Bool) p, beta z (P.length+n*L+p) = eta p) ∧
        (∀ (z : Fin n → Bool) p, recordWithTail o (synchronousPrefix h W z) w (P.length+n*L+p) =
          observe o (coordinate w p) 0) ∧
        Function.Injective (fun z : Fin n → Bool => address (synchronousPrefix P U z ++ w)) ∧
        (∀ (z : Fin n → Bool), Cut action initialConfiguration
          (front (recordWithTail o (synchronousPrefix h W z) w) (P.length+n*L)) (cuts z) ∧
          (cuts z).output.length ≤ k ∧
          (cuts z).output = (P.take k).take (cuts z).output.length ∧
          (cuts z).output <+: P.take k) ∧
        Function.Injective (fun z => ((cuts z).state,(cuts z).output)) ∧
        (∀ c, c ∈ states ↔ ∃ z, (cuts z).state = c) ∧
        2^n ≤ states.card*(k+1) := by
  classical
  have vWlen : ∀ i, V.length = (W i).length := fun i =>
    hVlen.trans ((hUlen i).symm.trans (hUWlen i))
  have wLen : ∀ i, (W i).length = L := fun i => (hUWlen i).symm.trans (hUlen i)
  obtain ⟨e,w,hw,hxlo,hxhi,highAll⟩ := fixed_finite_tail_all_histories o θ hθ
    s1 P h hP hPlen U W hU hUWlen lo hi hwidth hsupport invariant stemCert returnCert
  obtain ⟨eta,x,path,hp0,he,hs,hr,orbit,lowAll⟩ := fixed_omega_tail_all_histories
    o θ hθ s2 Q V h W hQ hV hQlen vWlen a y ha ha1 hane hslope hfixed hfeasible
  have z0 := zero_record o θ hθ .G0 [.L0] (by rfl)
  have z3 := zero_record o θ hθ .G0 [.L3] (by rfl)
  have processing := processing_of_safe_live_pair action initialConfiguration
    (OperationRecord o θ .closed) OperationFiniteSource safety liveness
    (address [.L0]) (address [.L3])
    (fun p => observe o (coordinate [.L0] p) 0) (fun p => observe o (coordinate [.L3] p) 0)
    z0.1 z3.1 z0.2 (by simp [address]) postprocessing
  refine ⟨e,w,eta,x,hw,hxlo,hxhi,?_⟩
  intro n
  choose beta X lowOmega lowPrefix lowFuture lowCoordinates lowRecord using lowAll
  let alpha : (Fin n → Bool) → ℕ → Label := fun z => address (synchronousPrefix P U z ++ w)
  let hRecord : (Fin n → Bool) → ℕ → Color := fun z => recordWithTail o (synchronousPrefix h W z) w
  let lRecord : (Fin n → Bool) → ℕ → Color := fun z => recordWithOmegaTail o (synchronousPrefix h W z) x
  have colorLength (z : Fin n → Bool) : (synchronousPrefix h W z).length = P.length+n*L := by
    rw [synchronous_length h W L wLen n z,← hPlen]
  have lowLength (z : Fin n → Bool) : (synchronousPrefix Q (fun _ => V) z).length = P.length+n*L := by
    rw [synchronous_length Q (fun _ => V) L (fun _ => hVlen) n z]
    omega
  have actualHigh (z : Fin n → Bool) : OperationRecord o θ .closed (alpha z) (hRecord z) ∧
      OperationFiniteSource (alpha z) := (highAll (List.ofFn z)).1 |> fun hrec =>
        ⟨hrec,(highAll (List.ofFn z)).2.1⟩
  have actualLow (z : Fin n → Bool) : OperationRecord o θ .closed (beta (List.ofFn z)) (lRecord z) :=
    lowRecord (List.ofFn z)
  have past (z : Fin n → Bool) (p : ℕ) (hp : p < P.length+n*L) : hRecord z p = lRecord z p := by
    have hpcs : p < (synchronousPrefix h W z).length := by rw [colorLength]; exact hp
    simp only [hRecord,lRecord,recordWithTail,recordWithOmegaTail,dif_pos hpcs]
  have futureLiteral (z : Fin n → Bool) (p : ℕ) : hRecord z (P.length+n*L+p) = observe o (coordinate w p) 0 := by
    have hh := (highAll (List.ofFn z)).2.2 p
    change recordWithTail o (synchronousPrefix h W z) w (P.length+n*L+p) = _
    rw [← colorLength z]
    exact hh
  have future (z z' : Fin n → Bool) (p : ℕ) : hRecord z (P.length+n*L+p) = hRecord z' (P.length+n*L+p) :=
    (futureLiteral z p).trans (futureLiteral z' p).symm
  have alphaAt (z : Fin n → Bool) (p : ℕ) (hp : p < P.length) : alpha z p = P[p] := by
    have hpa : p < (synchronousPrefix P U z).length := by simp only [synchronousPrefix,List.length_append]; omega
    simpa only [alpha,synchronousPrefix,List.getElem_append_left hp] using address_prefix _ w p hpa
  have betaAt (z : Fin n → Bool) (p : ℕ) (hp : p < Q.length) : beta (List.ofFn z) p = Q[p] := by
    have hpb : p < (synchronousPrefix Q (fun _ => V) z).length := by simp only [synchronousPrefix,List.length_append]; omega
    have hh := lowPrefix (List.ofFn z) p hpb
    change beta (List.ofFn z) p = (Q ++ choiceBlocks (fun _ => V) (List.ofFn z))[p] at hh
    exact hh.trans (List.getElem_append_left hp)
  have takeLength : (P.take k).length = k := by simp only [List.length_take,Nat.min_eq_left hk.le]
  have stemHigh (z : Fin n → Bool) (p : ℕ) (hp : p < (P.take k).length) : alpha z p = (P.take k)[p] := by
    have hpP : p < P.length := by rw [takeLength] at hp; omega
    simpa only [List.getElem_take] using alphaAt z p hpP
  have stemLow (z : Fin n → Bool) (p : ℕ) (hp : p < (P.take k).length) : beta (List.ofFn z) p = (P.take k)[p] := by
    have hpk : p < k := by rw [takeLength] at hp; exact hp
    have hpQ : p < Q.length := by omega
    calc beta (List.ofFn z) p = Q[p] := betaAt z p hpQ
         _ = P[p] := (sameStem p hpk).symm
         _ = (P.take k)[p] := by simp only [List.getElem_take]
  have different (z : Fin n → Bool) : alpha z (P.take k).length ≠ beta (List.ofFn z) (P.take k).length := by
    rw [takeLength,alphaAt z k hk,betaAt z k (by omega)]
    exact differentStem
  have inj := synchronous_address_injective P U L hUlen differentReturns w n
  obtain ⟨cuts,states,hcuts,joint,membership,count⟩ := original_operation_common_stem
    action initialConfiguration o θ .closed processing safety liveness alpha
    (fun z => beta (List.ofFn z)) hRecord lRecord (P.length+n*L) (P.take k)
    actualHigh actualLow past future stemHigh stemLow different inj
  refine ⟨fun z => beta (List.ofFn z),cuts,states,actualHigh,actualLow,?_,?_,futureLiteral,inj,?_,joint,membership,?_⟩
  · intro z p hp
    exact lowPrefix (List.ofFn z) p hp
  · intro z p
    have hh := lowFuture (List.ofFn z) p
    change beta (List.ofFn z) ((synchronousPrefix Q (fun _ => V) z).length+p) = eta p at hh
    rw [lowLength z] at hh
    exact hh
  · intro z
    simpa only [takeLength] using hcuts z
  · simpa only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,takeLength] using count


private theorem zero_inside_guard (s : Guard) : -1 < (0 : ℝ) ∧ 0 < supportUpper s := by
  rcases tail_arithmetic with ⟨_,ht,_,_,_,hphi⟩
  constructor
  · norm_num
  · cases s <;> simp only [supportUpper] <;> linarith

/-- Existing closed support and nonzero affine slope give strict support. -/
private theorem legal_compose_inside (s e : Guard) (w : List Label)
    (hw : LegalWord s e w) (x : ℝ) (hx : -1 < x ∧ x < supportUpper e) :
    -1 < compose w x ∧ compose w x < supportUpper s := by
  have hends : (-1 : ℝ) ≤ supportUpper e := by
    have h := zero_inside_guard e
    linarith
  exact compose_strict_inside w (-1) (supportUpper e) x (-1) (supportUpper s)
    hx.1 hx.2
    (literal_source_geometry.1 s e w (-1) hw ⟨le_rfl,hends⟩)
    (literal_source_geometry.1 s e w (supportUpper e) hw ⟨hends,le_rfl⟩)

/-- Actual root branches from one guard have disjoint interior images.
Closed branch endpoints are allowed to touch; strict tail inputs cannot hit them. -/
private theorem interior_branch_label_unique
    (s e f : Guard) (l m : Label) (x y : ℝ)
    (hl : nextGuard s l = some e) (hm : nextGuard s m = some f)
    (hx : -1 < x ∧ x < supportUpper e)
    (hy : -1 < y ∧ y < supportUpper f)
    (hvalue : branch l x = branch m y) : l = m := by
  rcases tail_arithmetic with ⟨htq,htp,ht1,hgp,hg1,hphi⟩
  have hxlo : 0 < g*(x+1) := mul_pos hgp (by linarith [hx.1])
  have hxhi : 0 < g*(supportUpper e-x) := mul_pos hgp (by linarith [hx.2])
  have hylo : 0 < g*(y+1) := mul_pos hgp (by linarith [hy.1])
  have hyhi : 0 < g*(supportUpper f-y) := mul_pos hgp (by linarith [hy.2])
  cases s <;> cases e <;> cases f <;> cases l <;> cases m <;>
    simp_all [nextGuard,supportUpper,branch,shift,phi,T2,g] <;> nlinarith

/-- Finite zero tails provide the actual equal-length legal-word injection needed
by original 39.2.2. No distinct-affine-map hypothesis is inserted. -/
private theorem legal_equal_length_zero_injective
    (s e f : Guard) (u v : List Label) (hlen : u.length = v.length)
    (hu : LegalWord s e u) (hv : LegalWord s f v)
    (hvalue : compose u 0 = compose v 0) : u = v := by
  induction u generalizing s e f v with
  | nil =>
    cases v with
    | nil => rfl
    | cons m v => simp at hlen
  | cons l u ih =>
    cases v with
    | nil => simp at hlen
    | cons m v =>
      have hlen' : u.length = v.length := by simpa using hlen
      cases hl : nextGuard s l with
      | none => simp [LegalWord,walk,hl] at hu
      | some q =>
        have hu' : LegalWord q e u := by simpa [LegalWord,walk,hl] using hu
        cases hm : nextGuard s m with
        | none => simp [LegalWord,walk,hm] at hv
        | some r =>
          have hv' : LegalWord r f v := by simpa [LegalWord,walk,hm] using hv
          have hlabels : l = m := interior_branch_label_unique s q r l m
            (compose u 0) (compose v 0) hl hm
            (legal_compose_inside q e u hu' 0 (zero_inside_guard e))
            (legal_compose_inside r f v hv' 0 (zero_inside_guard f)) hvalue
          subst m
          have hqr : q = r := Option.some.inj (hl.symm.trans hm)
          subst r
          have hgp : 0 < g := tail_arithmetic.2.2.2.1
          have htail : compose u 0 = compose v 0 := by
            change shift l-g*compose u 0 = shift l-g*compose v 0 at hvalue
            apply mul_left_cancel₀ (ne_of_gt hgp)
            linarith
          exact congrArg (List.cons l) (ih q e f v hlen' hu' hv' htail)

/-- The literal signed slope, retaining odd as well as even return lengths. -/
private theorem return_slope_control (L : ℕ) (hL : 0 < L) :
    -1 < (-g)^L ∧ (-g)^L < 1 ∧ (-g)^L ≠ 0 := by
  have hgp : 0 < g := tail_arithmetic.2.2.2.1
  have hg1 : g < 1 := tail_arithmetic.2.2.2.2.1
  have hsmall : |(-g)^L| < 1 := by
    rw [abs_pow,abs_neg,abs_of_pos hgp]
    exact pow_lt_one₀ hgp.le hg1 (by omega)
  exact ⟨(abs_lt.mp hsmall).1,(abs_lt.mp hsmall).2,
    pow_ne_zero _ (neg_ne_zero.mpr (ne_of_gt hgp))⟩

/-- Exact source formulas for both signs; A is the actual pair of translations. -/
noncomputable def canonicalAffineLo (A : Bool → ℝ) (a : ℝ) : ℝ :=
  if 0 < a then min (A false) (A true)/(1-a)
  else (min (A false) (A true)+a*max (A false) (A true))/(1-a^2)

noncomputable def canonicalAffineHi (A : Bool → ℝ) (a : ℝ) : ℝ :=
  if 0 < a then max (A false) (A true)/(1-a)
  else (max (A false) (A true)+a*min (A false) (A true))/(1-a^2)

/-- Endpoint contacts, signed width, invariance and minimality are all computed.
Minimality uses endpoint inequalities of the same invariant interval. -/
private theorem canonical_affine_hull (A : Bool → ℝ) (a : ℝ)
    (ha : -1 < a) (ha1 : a < 1) :
    let lo := canonicalAffineLo A a
    let hi := canonicalAffineHi A a
    lo ≤ hi ∧
    (A false ≠ A true → lo < hi) ∧
    (hi-lo = (max (A false) (A true)-min (A false) (A true)) /
      (if 0 < a then 1-a else 1+a)) ∧
    (if 0 < a then
      lo = min (A false) (A true)+a*lo ∧ hi = max (A false) (A true)+a*hi
     else
      lo = min (A false) (A true)+a*hi ∧ hi = max (A false) (A true)+a*lo) ∧
    (∀ i z, lo ≤ z → z ≤ hi → lo ≤ A i+a*z ∧ A i+a*z ≤ hi) ∧
    (∀ l u : ℝ, l ≤ u →
      (∀ i z, l ≤ z → z ≤ u → l ≤ A i+a*z ∧ A i+a*z ≤ u) →
      l ≤ lo ∧ hi ≤ u) := by
  let amin := min (A false) (A true)
  let amax := max (A false) (A true)
  let lo := canonicalAffineLo A a
  let hi := canonicalAffineHi A a
  have minuspos : 0 < 1-a := by linarith
  have pluspos : 0 < 1+a := by linarith
  have squarepos : 0 < 1-a^2 := by nlinarith [mul_pos minuspos pluspos]
  have delta : 0 ≤ amax-amin := sub_nonneg.mpr min_le_max
  have bounds : ∀ i, amin ≤ A i ∧ A i ≤ amax := by
    intro i
    cases i
    · exact ⟨min_le_left _ _,le_max_left _ _⟩
    · exact ⟨min_le_right _ _,le_max_right _ _⟩
  obtain ⟨imin,imax,hmin,hmax⟩ :
      ∃ imin imax : Bool, A imin = amin ∧ A imax = amax := by
    by_cases h : A false ≤ A true
    · exact ⟨false,true,(min_eq_left h).symm,(max_eq_right h).symm⟩
    · exact ⟨true,false,(min_eq_right (le_of_not_ge h)).symm,
        (max_eq_left (le_of_not_ge h)).symm⟩
  have width : hi-lo = (amax-amin)/(if 0 < a then 1-a else 1+a) := by
    by_cases apos : 0 < a
    · simp only [lo,hi,canonicalAffineLo,canonicalAffineHi,if_pos apos]
      dsimp [amin,amax]
      ring
    · simp only [lo,hi,canonicalAffineLo,canonicalAffineHi,if_neg apos]
      dsimp [amin,amax]
      field_simp [ne_of_gt squarepos,ne_of_gt pluspos]
      ring
  have denompos : 0 < (if 0 < a then 1-a else 1+a) := by
    split_ifs <;> assumption
  have ordered : lo ≤ hi := by
    have hd : 0 ≤ hi-lo := by rw [width]; exact div_nonneg delta denompos.le
    linarith
  have strict : A false ≠ A true → lo < hi := by
    intro hne
    have dp : 0 < amax-amin := by
      rcases lt_or_gt_of_ne hne with h | h
      · dsimp [amin,amax]
        rw [min_eq_left h.le,max_eq_right h.le]
        linarith
      · dsimp [amin,amax]
        rw [min_eq_right h.le,max_eq_left h.le]
        linarith
    have hd : 0 < hi-lo := by rw [width]; exact div_pos dp denompos
    linarith
  have contact : if 0 < a then lo=amin+a*lo ∧ hi=amax+a*hi
      else lo=amin+a*hi ∧ hi=amax+a*lo := by
    by_cases apos : 0 < a
    · simp only [lo,hi,canonicalAffineLo,canonicalAffineHi,if_pos apos]
      dsimp [amin,amax]
      constructor <;> field_simp [ne_of_gt minuspos] <;> ring
    · simp only [lo,hi,canonicalAffineLo,canonicalAffineHi,if_neg apos]
      dsimp [amin,amax]
      constructor <;> field_simp [ne_of_gt squarepos] <;> ring
  have invariant : ∀ i z, lo ≤ z → z ≤ hi → lo ≤ A i+a*z ∧ A i+a*z ≤ hi := by
    intro i z hzlo hzhi
    by_cases apos : 0 < a
    · have heq := contact
      rw [if_pos apos] at heq
      constructor
      · calc lo = amin+a*lo := heq.1
             _ ≤ A i+a*z := add_le_add (bounds i).1 (mul_le_mul_of_nonneg_left hzlo apos.le)
      · calc A i+a*z ≤ amax+a*hi := add_le_add (bounds i).2 (mul_le_mul_of_nonneg_left hzhi apos.le)
             _ = hi := heq.2.symm
    · have ale : a ≤ 0 := le_of_not_gt apos
      have heq := contact
      rw [if_neg apos] at heq
      constructor
      · calc lo = amin+a*hi := heq.1
             _ ≤ A i+a*z := add_le_add (bounds i).1 (mul_le_mul_of_nonpos_left hzhi ale)
      · calc A i+a*z ≤ amax+a*lo := add_le_add (bounds i).2 (mul_le_mul_of_nonpos_left hzlo ale)
             _ = hi := heq.2.symm
  have minimal : ∀ l u : ℝ, l ≤ u →
      (∀ i z, l ≤ z → z ≤ u → l ≤ A i+a*z ∧ A i+a*z ≤ u) →
      l ≤ lo ∧ hi ≤ u := by
    intro l u hlu hinv
    by_cases apos : 0 < a
    · have low := (hinv imin l le_rfl hlu).1
      have high := (hinv imax u hlu le_rfl).2
      rw [hmin] at low
      rw [hmax] at high
      change l ≤ canonicalAffineLo A a ∧ canonicalAffineHi A a ≤ u
      simp only [canonicalAffineLo,canonicalAffineHi,if_pos apos]
      constructor
      · apply (le_div_iff₀ minuspos).mpr
        change l*(1-a) ≤ amin
        nlinarith [low]
      · apply (div_le_iff₀ minuspos).mpr
        change amax ≤ u*(1-a)
        nlinarith [high]
    · have ale : a ≤ 0 := le_of_not_gt apos
      have low := (hinv imin u hlu le_rfl).1
      have high := (hinv imax l le_rfl hlu).2
      rw [hmin] at low
      rw [hmax] at high
      have lowerTwo : l ≤ amin+a*(amax+a*l) :=
        low.trans (add_le_add le_rfl (mul_le_mul_of_nonpos_left high ale))
      have upperTwo : amax+a*(amin+a*u) ≤ u :=
        (add_le_add le_rfl (mul_le_mul_of_nonpos_left low ale)).trans high
      change l ≤ canonicalAffineLo A a ∧ canonicalAffineHi A a ≤ u
      simp only [canonicalAffineLo,canonicalAffineHi,if_neg apos]
      constructor
      · apply (le_div_iff₀ squarepos).mpr
        change l*(1-a^2) ≤ amin+a*amax
        nlinarith [lowerTwo]
      · apply (div_le_iff₀ squarepos).mpr
        change amax+a*amin ≤ u*(1-a^2)
        nlinarith [upperTwo]
  exact ⟨ordered,strict,width,contact,invariant,minimal⟩

noncomputable def canonicalReturnLo (U : Bool → List Label) (L : ℕ) : ℝ :=
  canonicalAffineLo (fun i => compose (U i) 0) ((-g)^L)

noncomputable def canonicalReturnHi (U : Bool → List Label) (L : ℕ) : ℝ :=
  canonicalAffineHi (fun i => compose (U i) 0) ((-g)^L)

/-- The coefficient field Q(t), defined as the intersection of all real
subfields containing the literal Fibonacci coefficient t. -/
def coefficientField : Subfield ℝ where
  carrier := {x | ∀ F : Subfield ℝ, t ∈ F → x ∈ F}
  zero_mem' := fun F _ => F.zero_mem
  one_mem' := fun F _ => F.one_mem
  add_mem' := fun hx hy F ht => F.add_mem (hx F ht) (hy F ht)
  neg_mem' := fun hx F ht => F.neg_mem (hx F ht)
  mul_mem' := fun hx hy F ht => F.mul_mem (hx F ht) (hy F ht)
  inv_mem' := fun x hx F ht => F.inv_mem (hx F ht)

private theorem literal_coefficient_mem (w : List Label) : compose w 0 ∈ coefficientField := by
  have tmem : t ∈ coefficientField := fun F ht => ht
  have gmem : g ∈ coefficientField := by
    dsimp only [g]
    exact coefficientField.sub_mem
      (coefficientField.mul_mem (by simpa using coefficientField.intCast_mem (2 : ℤ)) tmem)
      coefficientField.one_mem
  have labelmem (l : Label) : shift l ∈ coefficientField := by
    cases l
    · exact coefficientField.neg_mem tmem
    · exact coefficientField.zero_mem
    · exact coefficientField.sub_mem coefficientField.one_mem tmem
    · exact coefficientField.one_mem
    · exact coefficientField.sub_mem
        (by simpa using coefficientField.intCast_mem (2 : ℤ)) tmem
  induction w with
  | nil => exact coefficientField.zero_mem
  | cons l w ih => exact coefficientField.sub_mem (labelmem l) (coefficientField.mul_mem gmem ih)

private theorem canonical_return_coefficient_mem (U : Bool → List Label) (L : ℕ) :
    canonicalReturnLo U L ∈ coefficientField ∧ canonicalReturnHi U L ∈ coefficientField := by
  have tmem : t ∈ coefficientField := fun F ht => ht
  have gmem : g ∈ coefficientField := by
    dsimp only [g]
    exact coefficientField.sub_mem
      (coefficientField.mul_mem (by simpa using coefficientField.intCast_mem (2 : ℤ)) tmem)
      coefficientField.one_mem
  have amem := coefficientField.pow_mem (coefficientField.neg_mem gmem) L
  have minmem : min (compose (U false) 0) (compose (U true) 0) ∈ coefficientField := by
    rcases le_total (compose (U false) 0) (compose (U true) 0) with h | h
    · rw [min_eq_left h]; exact literal_coefficient_mem _
    · rw [min_eq_right h]; exact literal_coefficient_mem _
  have maxmem : max (compose (U false) 0) (compose (U true) 0) ∈ coefficientField := by
    rcases le_total (compose (U false) 0) (compose (U true) 0) with h | h
    · rw [max_eq_right h]; exact literal_coefficient_mem _
    · rw [max_eq_left h]; exact literal_coefficient_mem _
  dsimp only [canonicalReturnLo, canonicalReturnHi, canonicalAffineLo, canonicalAffineHi]
  split_ifs
  · exact ⟨coefficientField.div_mem minmem (coefficientField.sub_mem coefficientField.one_mem amem),
      coefficientField.div_mem maxmem (coefficientField.sub_mem coefficientField.one_mem amem)⟩
  · exact ⟨coefficientField.div_mem (coefficientField.add_mem minmem (coefficientField.mul_mem amem maxmem))
        (coefficientField.sub_mem coefficientField.one_mem (coefficientField.pow_mem amem 2)),
      coefficientField.div_mem (coefficientField.add_mem maxmem (coefficientField.mul_mem amem minmem))
        (coefficientField.sub_mem coefficientField.one_mem (coefficientField.pow_mem amem 2))⟩

/-- Canonical support and minimality come from actual legal returns; strict width
comes from their literal difference, not a separately supplied geometric premise. -/
theorem canonical_legal_return_hull (s : Guard) (U : Bool → List Label)
    (L : ℕ) (hL : 0 < L) (hlen : ∀ i, (U i).length=L)
    (hlegal : ∀ i, LegalWord s s (U i)) :
    let lo := canonicalReturnLo U L
    let hi := canonicalReturnHi U L
    lo ≤ hi ∧
    (U false ≠ U true → lo < hi) ∧
    (∀ z ∈ Set.Icc lo hi, InSupport s z) ∧
    (∀ i z, lo ≤ z → z ≤ hi → lo ≤ compose (U i) z ∧ compose (U i) z ≤ hi) ∧
    (∀ l u : ℝ, l ≤ u →
      (∀ i z, l ≤ z → z ≤ u → l ≤ compose (U i) z ∧ compose (U i) z ≤ u) →
      l ≤ lo ∧ hi ≤ u) ∧
    (lo = hi ↔ U false = U true) ∧
    (lo ∈ coefficientField ∧ hi ∈ coefficientField) := by
  let A : Bool → ℝ := fun i => compose (U i) 0
  let a : ℝ := (-g)^L
  have slope := return_slope_control L hL
  have affine (i : Bool) (z : ℝ) : compose (U i) z = A i+a*z := by
    simpa only [zero_add,hlen] using literal_source_geometry.2.2.2.1 (U i) 0 z
  obtain ⟨ordered,strict,width,contact,invariant,minimal⟩ :=
    canonical_affine_hull A a slope.1 slope.2.1
  have realInvariant : ∀ i z, canonicalReturnLo U L ≤ z → z ≤ canonicalReturnHi U L →
      canonicalReturnLo U L ≤ compose (U i) z ∧ compose (U i) z ≤ canonicalReturnHi U L := by
    intro i z hzlo hzhi
    rw [affine]
    exact invariant i z hzlo hzhi
  have realMinimal : ∀ l u : ℝ, l ≤ u →
      (∀ i z, l ≤ z → z ≤ u → l ≤ compose (U i) z ∧ compose (U i) z ≤ u) →
      l ≤ canonicalReturnLo U L ∧ canonicalReturnHi U L ≤ u := by
    intro l u hlu h
    apply minimal l u hlu
    intro i z hzlo hzhi
    simpa only [affine] using h i z hzlo hzhi
  have guardOrdered : (-1 : ℝ) ≤ supportUpper s := by
    have h := zero_inside_guard s
    linarith
  have endpoints := realMinimal (-1) (supportUpper s) guardOrdered
    (fun i z hzlo hzhi => literal_source_geometry.1 s s (U i) z (hlegal i) ⟨hzlo,hzhi⟩)
  have singleton : canonicalReturnLo U L = canonicalReturnHi U L ↔ U false = U true := by
    constructor
    · intro heq
      by_contra hne
      have hs : canonicalReturnLo U L < canonicalReturnHi U L := strict (fun hz =>
        hne (legal_equal_length_zero_injective s s s (U false) (U true)
          ((hlen false).trans (hlen true).symm) (hlegal false) (hlegal true) hz))
      rw [heq] at hs
      exact (lt_irrefl _ hs)
    · intro heq
      simp only [canonicalReturnLo, canonicalReturnHi, canonicalAffineLo, canonicalAffineHi,
        heq, min_self, max_self]
  refine ⟨ordered,?_,?_,realInvariant,realMinimal,singleton,canonical_return_coefficient_mem U L⟩
  · intro hne
    apply strict
    intro heq
    exact hne (legal_equal_length_zero_injective s s s (U false) (U true)
      ((hlen false).trans (hlen true).symm) (hlegal false) (hlegal true) heq)
  · intro z hz
    exact ⟨endpoints.1.trans hz.1,hz.2.trans endpoints.2⟩

noncomputable def endpointCosts (lo hi : ℝ) (w : List Label) (cs : List Color) : List ℝ :=
  List.ofFn (fun r : Fin cs.length =>
    max (max (cut cs[r].val-compose (w.drop r.val) lo)
      (max 0 (compose (w.drop r.val) lo-cut (cs[r].val+1))))
      (max (cut cs[r].val-compose (w.drop r.val) hi)
        (max 0 (compose (w.drop r.val) hi-cut (cs[r].val+1)))))

/-- Every observed stem and return suffix is retained, on both actual sources. -/
noncomputable def familyEndpointCosts (P Q : List Label) (h : List Color)
    (U V : Bool → List Label) (W : Bool → List Color) (L : ℕ) : List ℝ :=
  endpointCosts (canonicalReturnLo U L) (canonicalReturnHi U L) P h ++
  endpointCosts (canonicalReturnLo V L) (canonicalReturnHi V L) Q h ++
  endpointCosts (canonicalReturnLo U L) (canonicalReturnHi U L) (U false) (W false) ++
  endpointCosts (canonicalReturnLo U L) (canonicalReturnHi U L) (U true) (W true) ++
  endpointCosts (canonicalReturnLo V L) (canonicalReturnHi V L) (V false) (W false) ++
  endpointCosts (canonicalReturnLo V L) (canonicalReturnHi V L) (V true) (W true)

noncomputable def familyEndpointBudget (P Q : List Label) (h : List Color)
    (U V : Bool → List Label) (W : Bool → List Color) (L : ℕ) : ℝ :=
  (familyEndpointCosts P Q h U V W L).foldr max 0

private theorem max_fold_nonnegative (xs : List ℝ) : 0 ≤ xs.foldr max 0 := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih => exact ih.trans (le_max_right _ _)

private theorem endpoint_certificate_of_budget (s e : Guard) (w : List Label)
    (cs : List Color) (lo hi : ℝ) (hw : LegalWord s e w)
    (hlo : InSupport e lo) (hhi : InSupport e hi) (costs : List ℝ)
    (part : ∀ c ∈ endpointCosts lo hi w cs, c ∈ costs) :
    EndpointCertificate (costs.foldr max 0) lo hi w cs := by
  intro r hr
  have hm : max (max (cut cs[r].val-compose (w.drop r) lo)
      (max 0 (compose (w.drop r) lo-cut (cs[r].val+1))))
      (max (cut cs[r].val-compose (w.drop r) hi)
        (max 0 (compose (w.drop r) hi-cut (cs[r].val+1)))) ∈ endpointCosts lo hi w cs :=
    List.mem_ofFn.mpr ⟨⟨r,hr⟩,rfl⟩
  have bound := List.le_max_of_le' 0 (part _ hm) le_rfl
  exact ⟨⟨suffix_supported s e w hw lo hlo r,(le_max_left _ _).trans bound⟩,
    ⟨suffix_supported s e w hw hi hhi r,(le_max_right _ _).trans bound⟩⟩

/-- The original finite endpoint maximum supplies the canonical high tail.
Certificates for all six indexed groups are derived from that same maximum. -/
private theorem endpoint_certificate_mono (a b lo hi : ℝ) (w : List Label) (cs : List Color)
    (hab : a ≤ b) (cert : EndpointCertificate a lo hi w cs) :
    EndpointCertificate b lo hi w cs := by
  intro r hr
  obtain ⟨⟨hslo,hblo⟩,⟨hshi,hbhi⟩⟩ := cert r hr
  exact ⟨⟨hslo,hblo.trans hab⟩,⟨hshi,hbhi.trans hab⟩⟩

private theorem family_endpoint_certificates
    (o : Ownership) (s1 s2 : Guard) (P Q : List Label) (h : List Color)
    (hP : LegalWord .G0 s1 P) (hQ : LegalWord .G0 s2 Q)
    (hPlen : P.length = h.length) (hQlen : Q.length = h.length)
    (U V : Bool → List Label) (W : Bool → List Color)
    (L : ℕ) (hL : 0 < L) (hlen : ∀ i, (U i).length = L)
    (hVlen : ∀ i, (V i).length = L)
    (hlegal : ∀ i, LegalWord s1 s1 (U i)) (hV : ∀ i, LegalWord s2 s2 (V i))
    (hcolors : ∀ i, (U i).length = (W i).length) :
    let θ := familyEndpointBudget P Q h U V W L
    0 ≤ θ ∧ (familyEndpointCosts P Q h U V W L).length = 2*h.length+4*L ∧
    EndpointCertificate θ (canonicalReturnLo U L) (canonicalReturnHi U L) P h ∧
    (∀ i, EndpointCertificate θ (canonicalReturnLo U L) (canonicalReturnHi U L) (U i) (W i)) ∧
    EndpointCertificate θ (canonicalReturnLo V L) (canonicalReturnHi V L) Q h ∧
    (∀ i, EndpointCertificate θ (canonicalReturnLo V L) (canonicalReturnHi V L) (V i) (W i)) := by
  let costs := familyEndpointCosts P Q h U V W L
  let θ := familyEndpointBudget P Q h U V W L
  have highHull := canonical_legal_return_hull s1 U L hL hlen hlegal
  have lowHull := canonical_legal_return_hull s2 V L hL hVlen hV
  have highLo := highHull.2.2.1 (canonicalReturnLo U L) ⟨le_rfl,highHull.1⟩
  have highHi := highHull.2.2.1 (canonicalReturnHi U L) ⟨highHull.1,le_rfl⟩
  have lowLo := lowHull.2.2.1 (canonicalReturnLo V L) ⟨le_rfl,lowHull.1⟩
  have lowHi := lowHull.2.2.1 (canonicalReturnHi V L) ⟨lowHull.1,le_rfl⟩
  have highStem : EndpointCertificate θ (canonicalReturnLo U L) (canonicalReturnHi U L) P h := by
    apply endpoint_certificate_of_budget .G0 s1 P h _ _ hP highLo highHi costs
    intro c hc
    simp only [costs,familyEndpointCosts,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hc))))
  have lowStem : EndpointCertificate θ (canonicalReturnLo V L) (canonicalReturnHi V L) Q h := by
    apply endpoint_certificate_of_budget .G0 s2 Q h _ _ hQ lowLo lowHi costs
    intro c hc
    simp only [costs,familyEndpointCosts,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc))))
  have highReturns : ∀ i, EndpointCertificate θ (canonicalReturnLo U L) (canonicalReturnHi U L)
      (U i) (W i) := by
    intro i
    apply endpoint_certificate_of_budget s1 s1 (U i) (W i) _ _ (hlegal i) highLo highHi costs
    intro c hc
    simp only [costs,familyEndpointCosts,List.mem_append]
    cases i
    · exact Or.inl (Or.inl (Or.inl (Or.inr hc)))
    · exact Or.inl (Or.inl (Or.inr hc))
  have lowReturns : ∀ i, EndpointCertificate θ (canonicalReturnLo V L) (canonicalReturnHi V L)
      (V i) (W i) := by
    intro i
    apply endpoint_certificate_of_budget s2 s2 (V i) (W i) _ _ (hV i) lowLo lowHi costs
    intro c hc
    simp only [costs,familyEndpointCosts,List.mem_append]
    cases i
    · exact Or.inl (Or.inr hc)
    · exact Or.inr hc
  have hθ : 0 ≤ θ := max_fold_nonnegative costs
  have wlen : ∀ i, (W i).length = L := fun i => (hcolors i).symm.trans (hlen i)
  have count : costs.length = 2*h.length+4*L := by
    simp only [costs,familyEndpointCosts,endpointCosts,List.length_append,List.length_ofFn,wlen]
    omega
  exact ⟨hθ,count,highStem,highReturns,lowStem,lowReturns⟩

theorem canonical_high_fixed_finite_tail
    (o : Ownership) (s1 s2 : Guard) (P Q : List Label) (h : List Color)
    (hP : LegalWord .G0 s1 P) (hQ : LegalWord .G0 s2 Q)
    (hPlen : P.length = h.length) (hQlen : Q.length = h.length)
    (U V : Bool → List Label) (W : Bool → List Color)
    (L : ℕ) (hL : 0 < L) (hlen : ∀ i, (U i).length = L)
    (hVlen : ∀ i, (V i).length = L)
    (hlegal : ∀ i, LegalWord s1 s1 (U i)) (hV : ∀ i, LegalWord s2 s2 (V i))
    (hdifferent : U false ≠ U true) (hcolors : ∀ i, (U i).length = (W i).length) :
    let θ := familyEndpointBudget P Q h U V W L
    0 ≤ θ ∧ (familyEndpointCosts P Q h U V W L).length = 2*h.length+4*L ∧
    EndpointCertificate θ (canonicalReturnLo V L) (canonicalReturnHi V L) Q h ∧
    (∀ i, EndpointCertificate θ (canonicalReturnLo V L) (canonicalReturnHi V L) (V i) (W i)) ∧
    ∃ (e : Guard) (w : List Label), LegalWord s1 e w ∧
      canonicalReturnLo U L < coordinate w 0 ∧ coordinate w 0 < canonicalReturnHi U L ∧
      ∀ zs : List Bool,
        OperationRecord o θ .closed (address ((P ++ choiceBlocks U zs) ++ w))
          (recordWithTail o (h ++ choiceBlocks W zs) w) ∧
        OperationFiniteSource (address ((P ++ choiceBlocks U zs) ++ w)) ∧
        ∀ p, recordWithTail o (h ++ choiceBlocks W zs) w
          ((h ++ choiceBlocks W zs).length+p) = observe o (coordinate w p) 0 := by
  let θ := familyEndpointBudget P Q h U V W L
  obtain ⟨hθ,count,highStem,highReturns,lowStem,lowReturns⟩ :=
    family_endpoint_certificates o s1 s2 P Q h hP hQ hPlen hQlen U V W L hL
      hlen hVlen hlegal hV hcolors
  have highHull := canonical_legal_return_hull s1 U L hL hlen hlegal
  refine ⟨hθ,count,lowStem,lowReturns,?_⟩
  exact fixed_finite_tail_all_histories o θ hθ s1 P h hP hPlen U W hlegal hcolors
    (canonicalReturnLo U L) (canonicalReturnHi U L) (highHull.2.1 hdifferent)
    highHull.2.2.1 highHull.2.2.2.1 highStem highReturns

/-- The actual canonical high hull and a canonical competing singleton supply
all synchronized sources and the arbitrary common-stem count. Geometry and the
identical competing word are derived from the legal families. The finite endpoint
budget derives the high certificates; the exact owned-endpoint orbit criterion
remains an explicit original feasibility condition. -/
theorem canonical_synchronous_common_stem {Configuration : Type*}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (θ : ℝ)
    (s1 s2 : Guard) (P Q : List Label) (h : List Color)
    (hP : LegalWord .G0 s1 P) (hQ : LegalWord .G0 s2 Q)
    (hPlen : P.length = h.length) (hQlen : Q.length = h.length)
    (U V : Bool → List Label) (W : Bool → List Color)
    (L : ℕ) (hL : 0 < L) (hU : ∀ i, LegalWord s1 s1 (U i))
    (hV : ∀ i, LegalWord s2 s2 (V i)) (hUlen : ∀ i, (U i).length = L)
    (hVlen : ∀ i, (V i).length = L) (hUWlen : ∀ i, (U i).length = (W i).length)
    (differentReturns : U false ≠ U true)
    (hbudget : familyEndpointBudget P Q h U V W L ≤ θ)
    (competingSingleton : canonicalReturnLo V L = canonicalReturnHi V L)
    (hfeasible : if 0 < (-g)^L then
      (CompetingT o θ s2 Q (V false) h W).Nonempty ∧
        canonicalReturnLo V L ∈ closure (CompetingT o θ s2 Q (V false) h W)
      else canonicalReturnLo V L ∈ CompetingT o θ s2 Q (V false) h W)
    (k : ℕ) (hk : k < P.length)
    (sameStem : ∀ p (hp : p < k), P[p] = Q[p]'(by omega))
    (differentStem : P[k] ≠ Q[k]'(by omega))
    (safety : ∀ alpha r, OperationRecord o θ .closed alpha r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = alpha p)
    (liveness : ∀ alpha r, OperationRecord o θ .closed alpha r → OperationFiniteSource alpha → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (postprocessing : ∀ alpha r, OperationRecord o θ .closed alpha r →
      ∀ (c d : Configuration) (q : ℕ) (out batch : List Label)
      (f : Color → Option (Configuration × List Label)),
      Run action (full r) ⟨initialConfiguration,0,[]⟩ ⟨c,q,out⟩ →
      action c = .acquire f → f (r q) = some (d,batch) →
      ∃ t, Drain action ⟨d,q+1,out++batch⟩ t) :
    ∃ (e : Guard) (w : List Label) (eta : ℕ → Label) (x : ℕ → ℝ),
      LegalWord s1 e w ∧ (canonicalReturnLo U L) < coordinate w 0 ∧ coordinate w 0 < (canonicalReturnHi U L) ∧
      ∀ n : ℕ, ∃ (beta : (Fin n → Bool) → ℕ → Label)
        (cuts : (Fin n → Bool) → Frame Configuration Label) (states : Finset Configuration),
        (∀ (z : Fin n → Bool), OperationRecord o θ .closed
          (address (synchronousPrefix P U z ++ w))
          (recordWithTail o (synchronousPrefix h W z) w) ∧
          OperationFiniteSource (address (synchronousPrefix P U z ++ w))) ∧
        (∀ (z : Fin n → Bool), OperationRecord o θ .closed (beta z)
          (recordWithOmegaTail o (synchronousPrefix h W z) x)) ∧
        (∀ (z : Fin n → Bool) p (hp : p < (synchronousPrefix Q V z).length),
          beta z p = (synchronousPrefix Q V z)[p]) ∧
        (∀ (z : Fin n → Bool) p, beta z (P.length+n*L+p) = eta p) ∧
        (∀ (z : Fin n → Bool) p, recordWithTail o (synchronousPrefix h W z) w (P.length+n*L+p) =
          observe o (coordinate w p) 0) ∧
        Function.Injective (fun z : Fin n → Bool => address (synchronousPrefix P U z ++ w)) ∧
        (∀ (z : Fin n → Bool), Cut action initialConfiguration
          (front (recordWithTail o (synchronousPrefix h W z) w) (P.length+n*L)) (cuts z) ∧
          (cuts z).output.length ≤ k ∧
          (cuts z).output = (P.take k).take (cuts z).output.length ∧
          (cuts z).output <+: P.take k) ∧
        Function.Injective (fun z => ((cuts z).state,(cuts z).output)) ∧
        (∀ c, c ∈ states ↔ ∃ z, (cuts z).state = c) ∧
        2^n ≤ states.card*(k+1) := by
  obtain ⟨budgetNonnegative,entryCount,stemBase,returnsBase,lowStemBase,lowReturnsBase⟩ :=
    family_endpoint_certificates o s1 s2 P Q h hP hQ hPlen hQlen U V W L hL
      hUlen hVlen hU hV hUWlen
  have hθ : 0 ≤ θ := budgetNonnegative.trans hbudget
  have stemCert := endpoint_certificate_mono _ θ _ _ P h hbudget stemBase
  have returnCert := fun i => endpoint_certificate_mono _ θ _ _ (U i) (W i) hbudget (returnsBase i)

  have highHull := canonical_legal_return_hull s1 U L hL hUlen hU
  have lowHull := canonical_legal_return_hull s2 V L hL hVlen hV
  have wordsEqual : V false = V true := lowHull.2.2.2.2.2.1.mp competingSingleton
  have familyEqual : V = fun _ => V false := by
    funext i
    cases i
    · rfl
    · exact wordsEqual.symm
  have slope := return_slope_control L hL
  have fixed : compose (V false) (canonicalReturnLo V L) = canonicalReturnLo V L := by
    have atLo := lowHull.2.2.2.1 false (canonicalReturnLo V L) le_rfl
      (le_of_eq competingSingleton)
    rw [← competingSingleton] at atLo
    exact le_antisymm atLo.2 atLo.1
  have result := original_synchronous_common_stem action initialConfiguration o θ hθ
    s1 s2 P Q h hP hQ hPlen hQlen U (V false) W L hL hU (hV false)
    hUlen (hVlen false) hUWlen differentReturns
    (canonicalReturnLo U L) (canonicalReturnHi U L) (highHull.2.1 differentReturns)
    highHull.2.2.1 highHull.2.2.2.1 stemCert returnCert
    ((-g)^L) (canonicalReturnLo V L) slope.1 slope.2.1 slope.2.2
    (by rw [hVlen false]) fixed hfeasible k hk sameStem differentStem safety liveness postprocessing
  simpa only [← familyEqual] using result

/-- A block-periodic actual source, with the guard and scalar future also periodic. -/
def PeriodicTail (s : Guard) (w : List Label) (z : ℝ) : Prop :=
  ∃ (a : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard),
    path 0 = s ∧ x 0 = z ∧
    (∀ p, nextGuard (path p) (a p) = some (path (p+1))) ∧
    (∀ p, InSupport (path p) (x p)) ∧
    (∀ p, x p = branch (a p) (x (p+1))) ∧
    (∀ p (hp : p < w.length), a p = w[p]) ∧
    (∀ p, a (p+w.length) = a p ∧ x (p+w.length) = x p ∧ path (p+w.length) = path p)

private theorem prefix_path_endpoint (s e : Guard) (w : List Label)
    (hw : LegalWord s e w) (a : ℕ → Label) (path : ℕ → Guard)
    (h0 : path 0 = s)
    (hedges : ∀ p, nextGuard (path p) (a p) = some (path (p+1)))
    (hprefix : ∀ p (hp : p < w.length), a p = w[p]) : path w.length = e := by
  induction w generalizing s a path with
  | nil =>
    have hse : s = e := by simpa [LegalWord,walk] using hw
    exact h0.trans hse
  | cons l w ih =>
    cases hn : nextGuard s l with
    | none => simp [LegalWord,walk,hn] at hw
    | some q =>
      have hw' : LegalWord q e w := by simpa [LegalWord,walk,hn] using hw
      have hq : path 1 = q := by
        have he := hedges 0
        rw [h0,hprefix 0 (by simp)] at he
        exact Option.some.inj (he.symm.trans hn)
      have htailPrefix : ∀ p (hp : p < w.length), a (p+1) = w[p] := by
        intro p hp
        exact hprefix (p+1) (by simp; omega)
      have htailEdges : ∀ p, nextGuard (path (p+1)) (a (p+1)) = some (path (p+1+1)) :=
        fun p => hedges (p+1)
      simpa only [List.length_cons,Nat.succ_eq_add_one] using
        ih q hw' (fun p => a (p+1)) (fun p => path (p+1)) hq
          (fun p => by simpa only [Nat.add_assoc] using htailEdges p) htailPrefix

private theorem periodic_tail_of_fixed_return (s : Guard) (w : List Label)
    (hw : LegalWord s s w) (hlen : 0 < w.length) (z : ℝ)
    (hz : InSupport s z) (hfixed : compose w z = z) : PeriodicTail s w z := by
  obtain ⟨a,x,path,h0,hx0,hedges,hsupp,hrec⟩ := lawful_tail s z hz
  obtain ⟨b,y,q,hq0,hy0,hbedges,hbsupp,hbrec,hprefix,hfuture,hyfuture⟩ :=
    prepend_legal_tail s s w hw a x path h0 hedges hsupp hrec
  have hyzero : y 0 = z := by rw [hy0,hx0,hfixed]
  have hyend : y w.length = y 0 := by
    have h := hyfuture 0
    simpa only [Nat.add_zero,hx0,hyzero] using h
  have hqend : q w.length = q 0 :=
    (prefix_path_endpoint s s w hw b q hq0 hbedges hprefix).trans hq0.symm
  have modstep (p : ℕ) : (p+1)%w.length = (p%w.length+1)%w.length := by
    rw [Nat.add_mod p 1 w.length]
    simpa only [Nat.mod_mod] using (Nat.add_mod (p%w.length) 1 w.length).symm
  refine ⟨fun p => b (p%w.length),fun p => y (p%w.length),fun p => q (p%w.length),
    by simpa using hq0,by simpa using hyzero,?_,?_,?_,?_,?_⟩
  · intro p
    change nextGuard (q (p%w.length)) (b (p%w.length)) = some (q ((p+1)%w.length))
    rw [modstep]
    by_cases h : p%w.length+1 < w.length
    · rw [Nat.mod_eq_of_lt h]
      exact hbedges (p%w.length)
    · have hend : p%w.length+1 = w.length := by have hb := Nat.mod_lt p hlen; omega
      rw [hend,Nat.mod_self]
      have he := hbedges (p%w.length)
      rw [hend,hqend] at he
      exact he
  · intro p
    exact hbsupp (p%w.length)
  · intro p
    change y (p%w.length) = branch (b (p%w.length)) (y ((p+1)%w.length))
    rw [modstep]
    by_cases h : p%w.length+1 < w.length
    · rw [Nat.mod_eq_of_lt h]
      exact hbrec (p%w.length)
    · have hend : p%w.length+1 = w.length := by have hb := Nat.mod_lt p hlen; omega
      rw [hend,Nat.mod_self]
      have he := hbrec (p%w.length)
      rw [hend,hyend] at he
      exact he
  · intro p hp
    change b (p%w.length) = w[p]
    rw [Nat.mod_eq_of_lt hp]
    exact hprefix p hp
  · intro p
    simp [Nat.add_mod]

/-- The actual extremal return blocks encode the canonical endpoints. Positive
slope repeats one block; negative slope alternates the two extremal blocks. -/
theorem canonical_periodic_endpoints (s : Guard) (U : Bool → List Label)
    (L : ℕ) (hL : 0 < L) (hlen : ∀ i, (U i).length = L)
    (hlegal : ∀ i, LegalWord s s (U i)) :
    ∃ imin imax : Bool,
      compose (U imin) 0 = min (compose (U false) 0) (compose (U true) 0) ∧
      compose (U imax) 0 = max (compose (U false) 0) (compose (U true) 0) ∧
      PeriodicTail s (if 0 < (-g)^L then U imin else U imin ++ U imax)
        (canonicalReturnLo U L) ∧
      PeriodicTail s (if 0 < (-g)^L then U imax else U imax ++ U imin)
        (canonicalReturnHi U L) := by
  let A : Bool → ℝ := fun i => compose (U i) 0
  let a : ℝ := (-g)^L
  let lo := canonicalReturnLo U L
  let hi := canonicalReturnHi U L
  have slope := return_slope_control L hL
  obtain ⟨ordered,strict,width,contact,invariant,minimal⟩ :=
    canonical_affine_hull A a slope.1 slope.2.1
  change (if 0 < a then
    lo = min (A false) (A true)+a*lo ∧ hi = max (A false) (A true)+a*hi
    else lo = min (A false) (A true)+a*hi ∧ hi = max (A false) (A true)+a*lo) at contact
  have hull := canonical_legal_return_hull s U L hL hlen hlegal
  have hslo : InSupport s lo := hull.2.2.1 lo ⟨le_rfl,hull.1⟩
  have hshi : InSupport s hi := hull.2.2.1 hi ⟨hull.1,le_rfl⟩
  obtain ⟨imin,imax,hmin,hmax⟩ : ∃ imin imax : Bool,
      A imin = min (A false) (A true) ∧ A imax = max (A false) (A true) := by
    rcases le_total (A false) (A true) with h | h
    · exact ⟨false,true,(min_eq_left h).symm,(max_eq_right h).symm⟩
    · exact ⟨true,false,(min_eq_right h).symm,(max_eq_left h).symm⟩
  have affine (i : Bool) (z : ℝ) : compose (U i) z = A i+a*z := by
    simpa only [zero_add,hlen] using literal_source_geometry.2.2.2.1 (U i) 0 z
  refine ⟨imin,imax,hmin,hmax,?_,?_⟩
  · by_cases hpos : 0 < a
    · rw [if_pos hpos]
      apply periodic_tail_of_fixed_return s (U imin) (hlegal imin) (by rw [hlen]; exact hL) lo hslo
      rw [if_pos hpos] at contact
      simpa only [affine,hmin] using contact.1.symm
    · rw [if_neg hpos]
      apply periodic_tail_of_fixed_return s (U imin ++ U imax)
        (legal_append s s s _ _ (hlegal imin) (hlegal imax))
        (by simp only [List.length_append,hlen]; omega) lo hslo
      rw [if_neg hpos] at contact
      rw [literal_source_geometry.2.2.2.2,affine,affine,hmin,hmax,← contact.2,← contact.1]
  · by_cases hpos : 0 < a
    · rw [if_pos hpos]
      apply periodic_tail_of_fixed_return s (U imax) (hlegal imax) (by rw [hlen]; exact hL) hi hshi
      rw [if_pos hpos] at contact
      simpa only [affine,hmax] using contact.2.symm
    · rw [if_neg hpos]
      apply periodic_tail_of_fixed_return s (U imax ++ U imin)
        (legal_append s s s _ _ (hlegal imax) (hlegal imin))
        (by simp only [List.length_append,hlen]; omega) hi hshi
      rw [if_neg hpos] at contact
      rw [literal_source_geometry.2.2.2.2,affine,affine,hmax,hmin,← contact.1,← contact.2]

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
