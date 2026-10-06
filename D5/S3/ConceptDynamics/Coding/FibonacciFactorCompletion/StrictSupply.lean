/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/StrictSupply
   generality: G
   anchors: []
   utility: none
   digest: Actual boundaries and active costs control the same paired source supply. -/

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

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

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
/-- Above the nonactive-slot bound, the complete actual paired supply is
equivalent to its actual stem, anchor and innermost return costs. -/
theorem actual_strict_cost_supply (model : Model) (o : Ownership) (b : ℝ)
    (execution : List Return) (hb : lam - rho < b) :
    ActualPairSupply model o b .strict execution ↔
      lam - g ^ 2 * chi * execute .high execution (initial .high model) < b ∧
      (model = .anchored → lam - g ^ 2 * chi * xSide .high < b) ∧
      StrictControl .high b execution (initial .high model) := by
  classical
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have root : g ^ 2 + 4 * g = 1 := by dsimp [g, t]; nlinarith
  have gp : 0 < g := by dsimp [g, t]; nlinarith
  have gq : g < 1 / 4 := by nlinarith
  have rp : 0 < rho := pow_pos gp 6
  have cp : 0 < chi := pow_pos gp 20
  have r1 : rho < 1 := pow_lt_one₀ gp.le (by linarith) (by decide)
  have c1 : chi < 1 := pow_lt_one₀ gp.le (by linarith) (by decide)
  have tg : t = (1 + g) / 2 := by dsimp [g]; ring
  have hp (j : Side) : 0 < hSide j ∧ hSide j < eSide j := by
    cases j <;> dsimp [hSide, eSide, c0, T2] <;>
      rw [tg] <;> constructor <;> linarith
  have ap (j : Side) : 0 < aSide j := mul_pos (sub_pos.mpr r1) (hp j).1
  have bp : 0 < b := by
    have hr : rho < 1 / 4096 := by
      have h := pow_lt_pow_left₀ gq gp.le (by decide : (6 : ℕ) ≠ 0)
      norm_num [rho] at h ⊢
      exact h
    have hl : 3 / 80 < lam := by dsimp [lam, T2]; rw [tg]; linarith
    linarith
  have app := literal_source_geometry.2.2.2.2
  have appendSupply (w v : List Label) (cs ds : List Color) (z : ℝ)
      (len : w.length = cs.length) :
      BlockSupply o b true (w ++ v) (cs ++ ds) z ↔
        BlockSupply o b true w cs (compose v z) ∧ BlockSupply o b true v ds z := by
    constructor
    · intro h
      constructor
      · intro p hpc
        have hpp : p < (cs ++ ds).length := by simp only [List.length_append]; omega
        obtain ⟨e, he, ho⟩ := h p hpp
        refine ⟨e, he, ?_⟩
        have hd : (w ++ v).drop p = w.drop p ++ v :=
          List.drop_append_of_le_length (by omega)
        simpa only [hd, app, List.getElem_append_left hpc] using ho
      · intro p hpd
        have hpp : cs.length + p < (cs ++ ds).length := by
          simp only [List.length_append]; omega
        obtain ⟨e, he, ho⟩ := h (cs.length + p) hpp
        refine ⟨e, he, ?_⟩
        have hd : (w ++ v).drop (cs.length + p) = v.drop p := by
          rw [List.drop_append, ← len, List.drop_eq_nil_of_le (by omega)]
          simp
        simpa only [hd, List.getElem_append_right (as := cs) (bs := ds)
          (i := cs.length + p) (by omega), Nat.add_sub_cancel_left] using ho
    · rintro ⟨hw, hv⟩ p hpc
      by_cases hleft : p < cs.length
      · obtain ⟨e, he, ho⟩ := hw p hleft
        refine ⟨e, he, ?_⟩
        have hd : (w ++ v).drop p = w.drop p ++ v :=
          List.drop_append_of_le_length (by omega)
        simpa only [hd, app, List.getElem_append_left hleft] using ho
      · have hright : p - cs.length < ds.length := by
          simp only [List.length_append] at hpc
          omega
        obtain ⟨e, he, ho⟩ := hv (p - cs.length) hright
        refine ⟨e, he, ?_⟩
        have hd : (w ++ v).drop p = v.drop (p - cs.length) := by
          rw [List.drop_append, len, List.drop_eq_nil_of_le (by omega)]
          simp
        simpa only [hd, List.getElem_append_right (as := cs) (bs := ds)
          (i := p) (by omega)] using ho
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
        dsimp [aSide]
        rw [pow_succ]
        ring
  have repeatCAct (j : Side) (n : ℕ) (D : ℝ) :
      compose (repeatWord C n) (c0 + sign j * D) = c0 + sign j * (chi ^ n * D) := by
    induction n with
    | zero => simp [repeatWord, compose]
    | succ n ih =>
        rw [repeatWord, app, ih,
          (paired_source_reconstruction j .original []).2.2.2.2.2.2.1]
        rw [pow_succ]
        ring
  have domain (j : Side) (D : ℝ) (hD : 0 < D ∧ D < hSide j) :
      0 ≤ c0 + sign j * D ∧ c0 + sign j * D ≤ T2 := by
    have hE := lt_trans hD.2 (hp j).2
    cases j <;> dsimp [sign, eSide, c0, T2] at * <;> constructor <;> linarith
  have csLength : ∀ n : ℕ, ((List.replicate n colorsD).flatten).length = 6 * n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih, colorsD]; omega
  have activeCostDrops (j : Side) (D : ℝ) (hD : D < hSide j) (n : ℕ) :
      lam - g ^ 2 * (hSide j - rho ^ (n + 1) * (hSide j - D)) <
        lam - g ^ 2 * (hSide j - rho ^ n * (hSide j - D)) := by
    have gain : 0 < g ^ 2 * rho ^ n * (1 - rho) * (hSide j - D) :=
      mul_pos (mul_pos (mul_pos (pow_pos gp 2) (pow_pos rp n))
        (sub_pos.mpr r1)) (sub_pos.mpr hD)
    rw [pow_succ rho n]
    nlinarith
  have activeInputLower (j : Side) (D : ℝ) (hD : D < hSide j) (n : ℕ) :
      D ≤ hSide j - rho ^ n * (hSide j - D) := by
    induction n with
    | zero =>
        simp only [pow_zero, one_mul]
        linarith
    | succ k ihk =>
        have hdrop := activeCostDrops j D hD k
        have gg : 0 < g ^ 2 := pow_pos gp 2
        have step : hSide j - rho ^ k * (hSide j - D) <
            hSide j - rho ^ (k + 1) * (hSide j - D) := by nlinarith
        exact ihk.trans step.le
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
        rw [(literal_full_slot_readout o b hb).1 j _ dn.1
          (le_of_lt (lt_trans dn.2 (hp j).2)), ih]
        have lower := activeInputLower j D hD.2 n
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
          · intro _
            exact h (by omega)
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
          · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right pl hD.1.le)
              (by simpa only [one_mul] using hD.2)
        exact (literal_full_slot_readout o b hb).2.2 _ (domain j _ dn).1 (domain j _ dn).2
  have returns (j : Side) (a : Return) (D : ℝ) (hD : 0 < D ∧ D < hSide j) :
      BlockSupply o b true (returnWord j a) (returnColors a) (c0 + sign j * D) ↔
        lam - g ^ 2 * chi ^ a.r * D < b := by
    have len : (repeatWord (block j) a.m).length =
        (List.replicate a.m colorsD).flatten.length := by
      rw [repeatLength, csLength]
      cases j <;> rfl
    rw [returnWord, returnColors, appendSupply _ _ _ _ _ len, repeatCAct]
    have pp := pow_pos cp a.r
    have pl : chi ^ a.r ≤ 1 := pow_le_one₀ cp.le c1.le
    have dn : 0 < chi ^ a.r * D ∧ chi ^ a.r * D < hSide j := by
      constructor
      · exact mul_pos pp hD.1
      · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right pl hD.1.le)
          (by simpa only [one_mul] using hD.2)
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
      rw [coordinate, sourcePrefix,
        List.drop_append_of_le_length (by rw [lengthEq]; omega), app]
      rfl
    constructor
    · intro h j p hp
      obtain ⟨err, herr, hread, hzero, hfuture⟩ := h j
      refine ⟨err p, herr p, ?_⟩
      rw [← coord j p hp]
      exact hread p hp
    · intro h j
      let choice (p : ℕ) (hp : p < (history model execution).length) : ℝ :=
        Classical.choose (h j p hp)
      let err (p : ℕ) : ℝ :=
        if hp : p < (history model execution).length then choice p hp else 0
      refine ⟨err, ?_, ?_, ?_, ?_⟩
      · intro p
        dsimp [err]
        split_ifs with hp
        · exact (Classical.choose_spec (h j p hp)).1
        · simpa using bp
      · intro p hp
        dsimp [err]
        rw [dif_pos hp, coord j p hp]
        exact (Classical.choose_spec (h j p hp)).2
      · intro p hp
        dsimp [err]
        rw [dif_neg (by omega)]
      · intro p
        have hz : err ((observedPrefix j model execution).length + p) = 0 := by
          dsimp [err]
          rw [dif_neg (by rw [lengthEq]; omega)]
        rw [hz, (paired_source_reconstruction j model execution).2.2.1]
  rw [pairErrors]
  have returnDomain (j : Side) (a : Return) (D : ℝ) (hD : 0 < D ∧ D < hSide j) :
      0 < returnMap j a D ∧ returnMap j a D < hSide j := by
    have rr := pow_pos rp a.m
    have rl : rho ^ a.m ≤ 1 := pow_le_one₀ rp.le r1.le
    have cc := pow_pos cp a.r
    have cl : chi ^ a.r ≤ 1 := pow_le_one₀ cp.le c1.le
    have cz : 0 < chi ^ a.r * D := mul_pos cc hD.1
    have ch : chi ^ a.r * D < hSide j :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right cl hD.1.le)
        (by simpa only [one_mul] using hD.2)
    have gap := mul_pos rr (sub_pos.mpr ch)
    have low := mul_le_mul_of_nonneg_right rl (sub_pos.mpr ch).le
    dsimp [returnMap]
    constructor <;> nlinarith
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
  have anchorTail (j : Side) :
      compose (anchor j model) (coordinate (tailPrefix j) 0) =
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
      stemSupply j _ (runDomain j execution model),
      extSupply j execution _ (initialDomain j model)]
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
    dsimp [returnMap]
    nlinarith
  have controlOrder (xs : List Return) (DH DL : ℝ) (ho : DH < DL)
      (hc : StrictControl .high b xs DH) : StrictControl .low b xs DL := by
    induction xs generalizing DH DL with
    | nil => trivial
    | cons a xs ih =>
        refine ⟨?_, ih _ _ (returnOrder a DH DL ho) hc.2⟩
        have gain := mul_pos (mul_pos (pow_pos gp 2) (pow_pos cp a.r)) (sub_pos.mpr ho)
        have h := hc.1
        nlinarith
  have io : initial .high model < initial .low model := by
    simpa only [List.take_zero, execute] using boundary.2.1 0
  have xo : xSide .high < xSide .low := by
    simpa only [List.take_nil, execute, initial] using
      (actual_complete_boundary_geometry .original []).2.1 0
  have eo : execute .high execution (initial .high model) <
      execute .low execution (initial .low model) := by
    simpa only [List.take_length] using boundary.2.1 execution.length
  constructor
  · intro h
    exact (wholeSide .high).mp (h .high)
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
        · intro hm
          have h := hanchor hm
          nlinarith

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
  have boundary := actual_complete_boundary_geometry model execution
  have costs := actual_strict_cost_supply model o b execution hb
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

set_option maxHeartbeats 1000000
open Filter Topology
open scoped Topology

/-- A consumed structural interface to the existing recursive guard. -/
theorem uniform_guard_trace_iff_split
    (K : ℕ) (d : ℝ) (strict : Bool) (j : Side)
    (execution : List Return) (D : ℝ) :
    GuardTrace K d strict j execution D ↔
      ∀ (before : List Return) (a : Return) (after : List Return),
        execution = before ++ a :: after →
          a.r ≤ K ∧ (a.r = K →
            if strict then d < execute j before D
            else d ≤ execute j before D) := by
  induction execution generalizing D with
  | nil =>
      constructor
      · intro _ before a after hsplit
        have hlen := congrArg List.length hsplit
        simp only [List.length_nil, List.length_append, List.length_cons] at hlen
        omega
      · intro _
        exact True.intro
  | cons first rest ih =>
      constructor
      · rintro ⟨hcap, hguard, hrest⟩ before a after hsplit
        cases before with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at hsplit
            rcases hsplit with ⟨rfl, rfl⟩
            exact ⟨hcap, hguard⟩
        | cons first' before =>
            simp only [List.cons_append, List.cons.injEq] at hsplit
            rcases hsplit with ⟨rfl, hsplit⟩
            simpa only [execute] using
              (ih (returnMap j first D)).mp hrest before a after hsplit
      · intro h
        have hfirst := h [] first rest rfl
        refine ⟨hfirst.1, hfirst.2, (ih (returnMap j first D)).mpr ?_⟩
        intro before a after hsplit
        have hsplit' : first :: rest = (first :: before) ++ a :: after := by
          simpa only [List.cons_append] using congrArg (List.cons first) hsplit
        simpa only [execute] using h (first :: before) a after hsplit'

/-- Budget enlargement keeps the identical error and literal-source witnesses. -/
theorem uniform_closed_supply_mono
    (model : Model) (o : Ownership) (execution : List Return)
    {small large : ℝ} (hbudget : small ≤ large)
    (hsupply : ActualPairSupply model o small .closed execution) :
    ActualPairSupply model o large .closed execution := by
  intro j
  rcases hsupply j with ⟨err, herr, hread, hzero, hfuture⟩
  refine ⟨err, ?_, hread, hzero, hfuture⟩
  intro p
  exact (herr p).trans hbudget

theorem exact_control_iff_split (j : Side) (budget : ℝ)
    (execution : List Return) (D : ℝ) :
    StrictControl j budget execution D ↔
      ∀ (before : List Return) (a : Return) (after : List Return),
        execution = before ++ a :: after →
          lam - g ^ 2 * chi ^ a.r * execute j before D < budget := by
  induction execution generalizing D with
  | nil =>
      constructor
      · intro _ before a after hsplit
        have hlen := congrArg List.length hsplit
        simp only [List.length_nil, List.length_append, List.length_cons] at hlen
        omega
      · intro _
        trivial
  | cons first rest ih =>
      constructor
      · rintro ⟨hfirst, hrest⟩ before a after hsplit
        cases before with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at hsplit
            rcases hsplit with ⟨rfl, rfl⟩
            exact hfirst
        | cons first' before =>
            simp only [List.cons_append, List.cons.injEq] at hsplit
            rcases hsplit with ⟨rfl, hsplit⟩
            simpa only [execute] using
              (ih (returnMap j first D)).mp hrest before a after hsplit
      · intro h
        refine ⟨h [] first rest rfl, (ih (returnMap j first D)).mpr ?_⟩
        intro before a after hsplit
        have hsplit' : first :: rest = (first :: before) ++ a :: after := by
          simpa only [List.cons_append] using congrArg (List.cons first) hsplit
        simpa only [execute] using h (first :: before) a after hsplit'


end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
