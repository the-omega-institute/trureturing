/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion
   generality: G
   anchors: []
   utility: none
   digest: Actual Fibonacci complete boundaries constrain their occurrence inputs. -/

import D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Constructions
import Mathlib.Data.Finset.Card

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

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
