/- GID: D5/S3/Estimation/DecisionRisk/CARFourStateReverseObstruction
   generality: I
   mirror-B: D5/B/S3/Estimation/DecisionRisk/CARFourStateReverseObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Estimation/DecisionRisk/CARFourStateReverseObstruction.claim; result=D5/S3/Estimation/DecisionRisk/CARFourStateReverseObstruction.result; claim=D5/S3/Estimation/DecisionRisk/CARFourStateReverseObstruction.claim
   digest: Four-state CAR experiments refute the coefficient two reverse bound, also with an actual common public partition seed. -/
import D5.S3.Estimation.DecisionRisk.CARRevelationScaling
import D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyTriangle
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators ENNReal
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.Estimation.DecisionRisk.CARApproximateRecovery
open D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
namespace D5.S3.Estimation.DecisionRisk.CARFourStateReverseObstruction
abbrev A := Fin 4
abbrev B := Block A
abbrev Seed := Option B × Option B

def wq (b : B) : ℚ := if b.1.card = 1 then 5/9 else if b.1.card = 4 then 4/9 else 0
def vq (b : B) : ℚ := if b.1.card = 2 then 2/9 else if b.1.card = 3 then 1/9 else 0
def rq (u : B → ℚ) (i : A) (b : B) : ℚ := if i ∈ b.1 then u b else 0
def hq (b c : B) : ℚ :=
  if b.1.card = 1 then (if c.1.card = 2 ∧ b.1 ⊆ c.1 then 1/3 else 0)
  else if b.1.card = 4 then (if c.1.card = 3 then 1/4 else 0)
  else if b = c then 1 else 0
def jq (b c : B) : ℚ :=
  if b.1.card = 2 then (if c.1.card = 4 then 1/6 else
    if c.1.card = 1 ∧ c.1 ⊆ b.1 then 5/12 else 0)
  else if b.1.card = 3 then (if c.1.card = 4 then 1 else 0)
  else if b = c then 1 else 0

def rejectLossQ (i : A) (a : Fin 5) : ℚ :=
  if a.val = 4 then 1/2 else if i.val = a.val then 0 else 1
def lists : Fin 6 → Finset A := ![{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}]
def listLossQ (i : A) (a : Fin 6) : ℚ := if i ∈ lists a then 0 else 1
def rejectMin (b : B) : ℚ :=
  if b.1.card = 1 then 0 else if b.1.card = 2 then 1/4 else
  if b.1.card = 3 then 3/8 else 1/2
def listMin (b : B) : ℚ := if b.1.card ≤ 2 then 0 else if b.1.card = 3 then 1/4 else 1/2

noncomputable section
def w (b : B) : ℝ := wq b
def v (b : B) : ℝ := vq b
def forward (b c : B) : ℝ := hq b c
def reverse (b c : B) : ℝ := jq b c
def prior (_ : A) : ℝ := 1/4
def rejectLoss (i : A) (a : Fin 5) : ℝ := rejectLossQ i a
def listLoss (i : A) (a : Fin 6) : ℝ := listLossQ i a
def mix (u : B → ℝ) (b : B) : ℝ := (1/2 : ℝ) * (if b.1.card = 1 then 1 else 0) + (1/2 : ℝ) * u b
def publicExperiment (p : Seed → ℝ) (P : Seed → Finpartition (Finset.univ : Finset A))
    (i : A) (o : Seed × B) : ℝ := if (P o.1).part i = o.2.1 then p o.1 else 0
def star (u z : B → ℝ) : ℝ := (1/2 : ℝ) * Finset.univ.sup' Finset.univ_nonempty
  (fun i : A => ∑ j ∈ Finset.univ.erase i, max (pair z i j - pair u i j) 0)

/-- The complete positive certificate, including unrestricted deficiencies and public experiments. -/
def Certificate : Prop :=
  (∀ b, 0 ≤ w b ∧ 0 ≤ v b) ∧
  (∀ i, ∑ b, row w i b = 1) ∧ (∀ i, ∑ b, row v i b = 1) ∧
  IsRowStochastic forward ∧ IsRowStochastic reverse ∧
  (∀ i, totalVariation (row v i) (channelOutput forward (row w i)) = 1/9) ∧
  (∀ i, totalVariation (row w i) (channelOutput reverse (row v i)) = 5/18) ∧
  (∀ i j, i ≠ j → pair w i j = 4/9 ∧ pair v i j = 4/9) ∧
  star w v = 0 ∧
  finiteBayesRisk prior rejectLoss (row w) = ENNReal.ofReal (2/9 : ℝ) ∧
  finiteBayesRisk prior rejectLoss (row v) = ENNReal.ofReal (1/2 : ℝ) ∧
  finiteBayesRisk prior listLoss (row w) = ENNReal.ofReal (2/9 : ℝ) ∧
  finiteBayesRisk prior listLoss (row v) = ENNReal.ofReal (1/9 : ℝ) ∧
  finiteDeficiency (row v) (row w) = ENNReal.ofReal (1/9 : ℝ) ∧
  finiteDeficiency (row w) (row v) = ENNReal.ofReal (5/18 : ℝ) ∧
  ENNReal.ofReal (min 1 (star w v + 2 * (finiteDeficiency (row v) (row w)).toReal)) <
    finiteDeficiency (row w) (row v) ∧
  (∀ c : ℝ, finiteDeficiency (row w) (row v) ≤
    ENNReal.ofReal (c * (finiteDeficiency (row v) (row w)).toReal) → 5/2 ≤ c) ∧
  star (mix w) (mix v) = 0 ∧
  finiteDeficiency (row (mix v)) (row (mix w)) = ENNReal.ofReal (1/18 : ℝ) ∧
  finiteDeficiency (row (mix w)) (row (mix v)) = ENNReal.ofReal (5/36 : ℝ) ∧
  (∃ (p : Seed → ℝ) (P Q : Seed → Finpartition (Finset.univ : Finset A)),
    (∀ s, 0 ≤ p s) ∧ (∑ s, p s = 1) ∧
    (∀ b, (∑ s, if b.1 ∈ (P s).parts then p s else 0) = mix w b) ∧
    (∀ b, (∑ s, if b.1 ∈ (Q s).parts then p s else 0) = mix v b) ∧
    (∃ (F : FiniteMarkovKernel (Seed × B) B) (R : FiniteMarkovKernel B (Seed × B)),
      (∀ i, channelOutput F.1 (publicExperiment p P i) = row (mix w) i) ∧
      (∀ i, channelOutput R.1 (row (mix w) i) = publicExperiment p P i)) ∧
    (∃ (F : FiniteMarkovKernel (Seed × B) B) (R : FiniteMarkovKernel B (Seed × B)),
      (∀ i, channelOutput F.1 (publicExperiment p Q i) = row (mix v) i) ∧
      (∀ i, channelOutput R.1 (row (mix v) i) = publicExperiment p Q i)) ∧
    finiteDeficiency (publicExperiment p Q) (publicExperiment p P) = ENNReal.ofReal (1/18 : ℝ) ∧
    finiteDeficiency (publicExperiment p P) (publicExperiment p Q) = ENNReal.ofReal (5/36 : ℝ) ∧
    ENNReal.ofReal (min 1 (star (mix w) (mix v) +
      2 * (finiteDeficiency (publicExperiment p Q) (publicExperiment p P)).toReal)) <
      finiteDeficiency (publicExperiment p P) (publicExperiment p Q))

/-- The coefficient-two bound at this actual certified four-state pair. -/
def claim : Prop := Certificate → finiteDeficiency (row w) (row v) ≤
  ENNReal.ofReal (min 1 (star w v + 2 * (finiteDeficiency (row v) (row w)).toReal))

/-- The complete actual certificate makes the proposed reverse bound false. -/
theorem result : ¬ claim := by
  have qw : (∀ b, 0 ≤ wq b) ∧ (∀ i, ∑ b, rq wq i b = 1) := by decide +kernel
  have qv : (∀ b, 0 ≤ vq b) ∧ (∀ i, ∑ b, rq vq i b = 1) := by decide +kernel
  have qh : (∀ b c, 0 ≤ hq b c) ∧ (∀ b, ∑ c, hq b c = 1) := by decide +kernel
  have qj : (∀ b c, 0 ≤ jq b c) ∧ (∀ b, ∑ c, jq b c = 1) := by decide +kernel
  have qt : (∀ i, (1/2 : ℚ) * ∑ c, |rq vq i c - ∑ b, rq wq i b * hq b c| = 1/9) ∧
      (∀ i, (1/2 : ℚ) * ∑ c, |rq wq i c - ∑ b, rq vq i b * jq b c| = 5/18) := by decide +kernel
  have qp : ∀ i j : A, i ≠ j →
      (∑ b : B, if i ∈ b.1 ∧ j ∈ b.1 then wq b else 0) = 4/9 ∧
      (∑ b : B, if i ∈ b.1 ∧ j ∈ b.1 then vq b else 0) = 4/9 := by decide +kernel
  have castrow (u : B → ℚ) (i : A) (b : B) : row (fun b => (u b : ℝ)) i b = (rq u i b : ℝ) := by
    simp only [row, rq]; split_ifs <;> norm_cast
  have hw : ∀ b, 0 ≤ w b := by intro b; dsimp only [w]; exact_mod_cast qw.1 b
  have hv : ∀ b, 0 ≤ v b := by intro b; dsimp only [v]; exact_mod_cast qv.1 b
  have hwr : ∀ i, ∑ b, row w i b = 1 := by
    intro i; change (∑ b, row (fun b => (wq b : ℝ)) i b) = 1
    simp only [castrow]; exact_mod_cast qw.2 i
  have hvr : ∀ i, ∑ b, row v i b = 1 := by
    intro i; change (∑ b, row (fun b => (vq b : ℝ)) i b) = 1
    simp only [castrow]; exact_mod_cast qv.2 i
  have hH : IsRowStochastic forward := by
    constructor
    · intro b c; dsimp only [forward]; exact_mod_cast qh.1 b c
    · intro b; dsimp only [forward]; exact_mod_cast qh.2 b
  have hJ : IsRowStochastic reverse := by
    constructor
    · intro b c; dsimp only [reverse]; exact_mod_cast qj.1 b c
    · intro b; dsimp only [reverse]; exact_mod_cast qj.2 b
  let H : FiniteMarkovKernel B B := ⟨forward, hH⟩
  let J : FiniteMarkovKernel B B := ⟨reverse, hJ⟩
  have htH : ∀ i, totalVariation (row v i) (channelOutput forward (row w i)) = 1/9 := by
    intro i; change totalVariation (row (fun b => (vq b : ℝ)) i) (channelOutput (fun b c => (hq b c : ℝ)) (row (fun b => (wq b : ℝ)) i)) = _
    simp only [totalVariation, channelOutput, castrow]
    have hh := congrArg (fun x : ℚ => (x : ℝ)) (qt.1 i)
    push_cast at hh
    exact hh
  have htJ : ∀ i, totalVariation (row w i) (channelOutput reverse (row v i)) = 5/18 := by
    intro i; change totalVariation (row (fun b => (wq b : ℝ)) i) (channelOutput (fun b c => (jq b c : ℝ)) (row (fun b => (vq b : ℝ)) i)) = _
    simp only [totalVariation, channelOutput, castrow]
    have hh := congrArg (fun x : ℚ => (x : ℝ)) (qt.2 i)
    push_cast at hh
    exact hh
  have hp : ∀ i j, i ≠ j → pair w i j = 4/9 ∧ pair v i j = 4/9 := by
    intro i j hij
    have h := qp i j hij
    simp only [pair, w, v]
    constructor
    · have hh := congrArg (fun x : ℚ => (x : ℝ)) h.1
      push_cast at hh
      simpa only [apply_ite, Rat.cast_zero] using hh
    · have hh := congrArg (fun x : ℚ => (x : ℝ)) h.2
      push_cast at hh
      simpa only [apply_ite, Rat.cast_zero] using hh
  have hs : star w v = 0 := by
    unfold star
    have he : ∀ i : A, (∑ j ∈ Finset.univ.erase i, max (pair v i j - pair w i j) 0) = 0 := by
      intro i; apply Finset.sum_eq_zero; intro j hj
      have h := hp i j (Finset.ne_of_mem_erase hj).symm
      rw [h.1, h.2]; norm_num
    simp only [he, Finset.sup'_const, mul_zero]
  have risk {n : ℕ} [NeZero n] (u : B → ℚ) (l : A → Fin n → ℚ) (m : B → ℚ)
      (hu : ∀ b, 0 ≤ u b)
      (hm : ∀ b a, m b ≤ ∑ i : A, (1/4 : ℚ) * (if i ∈ b.1 then 1 else 0) * l i a)
      (ha : ∀ b, ∃ a : Fin n, m b = ∑ i : A, (1/4 : ℚ) * (if i ∈ b.1 then 1 else 0) * l i a) :
      finiteBayesRisk prior (fun i a => (l i a : ℝ)) (row (fun b => (u b : ℝ))) =
        ENNReal.ofReal ((∑ b, u b * m b : ℚ) : ℝ) := by
    classical
    choose f hf using ha
    have expand (d : B → Fin n → ℝ) :
        finiteBayesCost prior (fun i a => (l i a : ℝ)) (row (fun b => (u b : ℝ))) d =
          ∑ b, (u b : ℝ) * ∑ a, d b a *
            ∑ i : A, (1/4 : ℝ) * (if i ∈ b.1 then 1 else 0) * (l i a : ℝ) := by
      simp only [finiteBayesCost, channelOutput, prior, Finset.mul_sum, Finset.sum_mul]
      calc
        (∑ i : A, ∑ a : Fin n, ∑ b : B,
          (1/4 : ℝ) * (row (fun b => (u b : ℝ)) i b * d b a * (l i a : ℝ))) =
            ∑ i : A, ∑ b : B, ∑ a : Fin n,
              (1/4 : ℝ) * (row (fun b => (u b : ℝ)) i b * d b a * (l i a : ℝ)) := by
                apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
        _ = ∑ b : B, ∑ i : A, ∑ a : Fin n,
              (1/4 : ℝ) * (row (fun b => (u b : ℝ)) i b * d b a * (l i a : ℝ)) := Finset.sum_comm
        _ = ∑ b : B, ∑ a : Fin n, ∑ i : A,
              (1/4 : ℝ) * (row (fun b => (u b : ℝ)) i b * d b a * (l i a : ℝ)) := by
                apply Finset.sum_congr rfl; intro b _; exact Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl; intro b _
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro i _
          simp only [row]; split_ifs <;> ring
    have coeff (b : B) (a : Fin n) :
        ((∑ i : A, (1/4 : ℚ) * (if i ∈ b.1 then 1 else 0) * l i a : ℚ) : ℝ) =
          ∑ i : A, (1/4 : ℝ) * (if i ∈ b.1 then 1 else 0) * (l i a : ℝ) := by
      push_cast
      simp only [apply_ite, Rat.cast_one, Rat.cast_zero]
    let d : FiniteMarkovKernel B (Fin n) :=
      ⟨fun b a => if f b = a then 1 else 0,
        ⟨by intro b a; dsimp only; split_ifs <;> norm_num, by intro b; simp⟩⟩
    have hd : finiteBayesCost prior (fun i a => (l i a : ℝ)) (row (fun b => (u b : ℝ))) d.1 =
        ((∑ b, u b * m b : ℚ) : ℝ) := by
      rw [expand]
      simp only [d, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      push_cast
      apply Finset.sum_congr rfl; intro b _
      congr 1
      rw [← coeff]; exact congrArg (fun x : ℚ => (x : ℝ)) (hf b).symm
    apply le_antisymm
    · exact (iInf_le _ d).trans_eq (congrArg ENNReal.ofReal hd)
    · apply le_iInf; intro k
      apply ENNReal.ofReal_le_ofReal
      rw [expand]; push_cast
      apply Finset.sum_le_sum; intro b _
      apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hu b)
      calc
        (m b : ℝ) = (∑ a, k.1 b a) * (m b : ℝ) := by rw [k.2.2, one_mul]
        _ = ∑ a, k.1 b a * (m b : ℝ) := Finset.sum_mul _ _ _
        _ ≤ _ := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          (by rw [← coeff]; exact_mod_cast hm b a) (k.2.1 b a)
  have qr : (∀ b a, rejectMin b ≤ ∑ i : A, (1/4 : ℚ) * (if i ∈ b.1 then 1 else 0) * rejectLossQ i a) ∧
      (∀ b, ∃ a : Fin 5, rejectMin b = ∑ i : A, (1/4 : ℚ) * (if i ∈ b.1 then 1 else 0) * rejectLossQ i a) := by decide +kernel
  have ql : (∀ b a, listMin b ≤ ∑ i : A, (1/4 : ℚ) * (if i ∈ b.1 then 1 else 0) * listLossQ i a) ∧
      (∀ b, ∃ a : Fin 6, listMin b = ∑ i : A, (1/4 : ℚ) * (if i ∈ b.1 then 1 else 0) * listLossQ i a) := by decide +kernel
  have qsum : (∑ b, wq b * rejectMin b) = 2/9 ∧ (∑ b, vq b * rejectMin b) = 1/2 ∧
      (∑ b, wq b * listMin b) = 2/9 ∧ (∑ b, vq b * listMin b) = 1/9 := by decide +kernel
  have rwR : finiteBayesRisk prior rejectLoss (row w) = ENNReal.ofReal (2/9 : ℝ) := by
    change finiteBayesRisk prior (fun i a => (rejectLossQ i a : ℝ)) (row (fun b => (wq b : ℝ))) = ENNReal.ofReal (2/9 : ℝ)
    have hh := risk wq rejectLossQ rejectMin qw.1 qr.1 qr.2
    rw [qsum.1] at hh
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at hh
    exact hh
  have rvR : finiteBayesRisk prior rejectLoss (row v) = ENNReal.ofReal (1/2 : ℝ) := by
    change finiteBayesRisk prior (fun i a => (rejectLossQ i a : ℝ)) (row (fun b => (vq b : ℝ))) = ENNReal.ofReal (1/2 : ℝ)
    have hh := risk vq rejectLossQ rejectMin qv.1 qr.1 qr.2
    rw [qsum.2.1] at hh
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at hh
    exact hh
  have rwL : finiteBayesRisk prior listLoss (row w) = ENNReal.ofReal (2/9 : ℝ) := by
    change finiteBayesRisk prior (fun i a => (listLossQ i a : ℝ)) (row (fun b => (wq b : ℝ))) = ENNReal.ofReal (2/9 : ℝ)
    have hh := risk wq listLossQ listMin qw.1 ql.1 ql.2
    rw [qsum.2.2.1] at hh
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at hh
    exact hh
  have rvL : finiteBayesRisk prior listLoss (row v) = ENNReal.ofReal (1/9 : ℝ) := by
    change finiteBayesRisk prior (fun i a => (listLossQ i a : ℝ)) (row (fun b => (vq b : ℝ))) = ENNReal.ofReal (1/9 : ℝ)
    have hh := risk vq listLossQ listMin qv.1 ql.1 ql.2
    rw [qsum.2.2.2] at hh
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at hh
    exact hh
  have hW : IsRowStochastic (row w) := ⟨by intro i b; unfold row; split_ifs; exact hw b; exact le_rfl, hwr⟩
  have hV : IsRowStochastic (row v) := ⟨by intro i b; unfold row; split_ifs; exact hv b; exact le_rfl, hvr⟩
  have hprior : (∀ i, 0 ≤ prior i) ∧ ∑ i, prior i = 1 := by norm_num [prior, Fin.sum_univ_succ]
  have br : ∀ i a, 0 ≤ rejectLoss i a ∧ rejectLoss i a ≤ 1 := by
    intro i a; simp only [rejectLoss, rejectLossQ]; split_ifs <;> norm_num
  have bl : ∀ i a, 0 ≤ listLoss i a ∧ listLoss i a ≤ 1 := by
    intro i a; simp only [listLoss, listLossQ]; split_ifs <;> norm_num
  have upper {X Y : A → B → ℝ} (K : FiniteMarkovKernel B B) (e : ℝ)
      (he : ∀ i, totalVariation (Y i) (channelOutput K.1 (X i)) = e) :
      finiteDeficiency Y X ≤ ENNReal.ofReal e := by
    apply (iInf_le _ K).trans_eq
    congr 1
    simp only [uniformSimulationError, he, Finset.sup'_const]
  have uf := upper H (1/9) htH
  have ur := upper J (5/18) htJ
  have lf := deficiency_risk_bound prior listLoss (row w) (row v) hprior hW hV bl
  have lr := deficiency_risk_bound prior rejectLoss (row v) (row w) hprior hV hW br
  rw [rwL, rvL] at lf
  rw [rvR, rwR] at lr
  have df : finiteDeficiency (row v) (row w) = ENNReal.ofReal (1/9 : ℝ) := by
    apply le_antisymm uf
    have hn := ne_top_of_le_ne_top ENNReal.ofReal_ne_top uf
    have hh := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hn⟩)).mpr lf
    rw [ENNReal.toReal_add (by finiteness) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top uf)] at hh
    norm_num at hh ⊢
    exact (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top uf)).mpr (by linarith)
  have dr : finiteDeficiency (row w) (row v) = ENNReal.ofReal (5/18 : ℝ) := by
    apply le_antisymm ur
    have hn := ne_top_of_le_ne_top ENNReal.ofReal_ne_top ur
    have hh := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hn⟩)).mpr lr
    rw [ENNReal.toReal_add (by finiteness) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ur)] at hh
    norm_num at hh ⊢
    exact (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ur)).mpr (by linarith)
  have violation : ENNReal.ofReal (min 1 (star w v + 2 * (finiteDeficiency (row v) (row w)).toReal)) <
      finiteDeficiency (row w) (row v) := by rw [hs, df, dr]; norm_num
  have necessary : ∀ c : ℝ, finiteDeficiency (row w) (row v) ≤
      ENNReal.ofReal (c * (finiteDeficiency (row v) (row w)).toReal) → 5/2 ≤ c := by
    intro c hc; rw [df, dr] at hc; norm_num at hc
    have hh := ENNReal.ofReal_le_ofReal_iff'.mp hc
    rcases hh with hh | hh <;> linarith
  have scaling := CARRevelationScaling.result w v hw hv hwr hvr
  have scaled := scaling.1 (1/2) (by norm_num) (by norm_num)
  have dsf : finiteDeficiency (row (mix v)) (row (mix w)) = ENNReal.ofReal (1/18 : ℝ) := by
    have hh := scaled.1
    norm_num only [show (1 : ℝ) - 1/2 = 1/2 by norm_num] at hh
    change finiteDeficiency (row (mix v)) (row (mix w)) = _ at hh
    rw [df, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)] at hh
    norm_num only [show (1/2 : ℝ) * (1/9) = 1/18 by norm_num] at hh
    exact hh
  have dsr : finiteDeficiency (row (mix w)) (row (mix v)) = ENNReal.ofReal (5/36 : ℝ) := by
    have hh := scaled.2
    norm_num only [show (1 : ℝ) - 1/2 = 1/2 by norm_num] at hh
    change finiteDeficiency (row (mix w)) (row (mix v)) = _ at hh
    rw [dr, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)] at hh
    norm_num only [show (1/2 : ℝ) * (5/18) = 5/36 by norm_num] at hh
    exact hh
  have hsm : star (mix w) (mix v) = 0 := by
    have he : ∀ i j, i ≠ j → pair (mix v) i j = pair (mix w) i j := by
      intro i j hij
      have hpw := (hp i j hij).1
      have hpv := (hp i j hij).2
      have pe (u : B → ℝ) : pair (mix u) i j =
          (1/2 : ℝ) * (∑ b : B, if i ∈ b.1 ∧ j ∈ b.1 then (if b.1.card = 1 then 1 else 0) else 0) +
          (1/2 : ℝ) * pair u i j := by
        unfold pair mix
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro b _; split_ifs <;> ring
      rw [pe, pe, hpw, hpv]
    unfold star
    have hz : ∀ i : A, (∑ j ∈ Finset.univ.erase i, max (pair (mix v) i j - pair (mix w) i j) 0) = 0 := by
      intro i; apply Finset.sum_eq_zero; intro j hj
      rw [he i j (Finset.ne_of_mem_erase hj).symm]; norm_num
    simp only [hz, Finset.sup'_const, mul_zero]
  norm_num only [show (1 : ℝ) - 1/2 = 1/2 by norm_num] at scaling
  obtain ⟨p, P, Q, hp0, hp1, hPw, hQv, eP, eQ⟩ :=
    scaling.2.2 (by decide) (1/2) (by norm_num) (by norm_num)
  norm_num only [show (1 : ℝ) - 1/2 = 1/2 by norm_num] at hPw hQv eP eQ
  -- Exact public deficiency transport follows from the four common equivalence kernels.
  have transport {O T I L : Type} [Fintype O] [Fintype T] [Fintype I] [Fintype L]
      (X : A → O → ℝ) (Y : A → T → ℝ) (U : A → I → ℝ) (V : A → L → ℝ)
      (F : FiniteMarkovKernel O I) (R : FiniteMarkovKernel L T)
      (hF : ∀ i, channelOutput F.1 (X i) = U i)
      (hR : ∀ i, channelOutput R.1 (V i) = Y i) :
      finiteDeficiency Y X ≤ finiteDeficiency V U := by
    apply le_iInf; intro K
    let C : O → T → ℝ := fun o t => ∑ b, ∑ c, F.1 o b * K.1 b c * R.1 c t
    have hC : IsRowStochastic C := by
      constructor
      · intro o t; exact Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ =>
          mul_nonneg (mul_nonneg (F.2.1 o b) (K.2.1 b c)) (R.2.1 c t)
      · intro o; dsimp only [C]
        rw [Finset.sum_comm]
        calc
          (∑ b : I, ∑ t : T, ∑ c : L, F.1 o b * K.1 b c * R.1 c t) =
              ∑ b : I, ∑ c : L, ∑ t : T, F.1 o b * K.1 b c * R.1 c t := by
                apply Finset.sum_congr rfl; intro b _; exact Finset.sum_comm
          _ = 1 := by
            simp_rw [← Finset.mul_sum, R.2.2, mul_one, ← Finset.mul_sum, K.2.2, mul_one]
            exact F.2.2 o
    let CK : FiniteMarkovKernel O T := ⟨C, hC⟩
    apply (iInf_le _ CK).trans
    apply ENNReal.ofReal_le_ofReal
    apply Finset.sup'_le; intro i _
    have hc : channelOutput C (X i) = channelOutput R.1 (channelOutput K.1 (U i)) := by
      rw [← hF i]; funext t
      simp only [channelOutput, C, Finset.mul_sum, Finset.sum_mul]
      calc
        (∑ o : O, ∑ b : I, ∑ c : L, X i o * (F.1 o b * K.1 b c * R.1 c t)) =
            ∑ b : I, ∑ o : O, ∑ c : L, X i o * (F.1 o b * K.1 b c * R.1 c t) := Finset.sum_comm
        _ = ∑ b : I, ∑ c : L, ∑ o : O, X i o * (F.1 o b * K.1 b c * R.1 c t) := by
          apply Finset.sum_congr rfl; intro b _; exact Finset.sum_comm
        _ = ∑ c : L, ∑ b : I, ∑ o : O, X i o * (F.1 o b * K.1 b c * R.1 c t) := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl; intro c _
          apply Finset.sum_congr rfl; intro b _
          apply Finset.sum_congr rfl; intro o _; ring
    change totalVariation (Y i) (channelOutput C (X i)) ≤ _
    rw [hc, ← hR i]
    exact (D5.S3.TotalVariation.DataProcessing.total_variation_channel_le
      (V i) (channelOutput K.1 (U i)) R.1 R.2).trans
      (Finset.le_sup' (fun state : A => totalVariation (V state)
        (channelOutput K.1 (U state))) (Finset.mem_univ i))
  obtain ⟨FP, RP, hFP, hRP⟩ := eP
  obtain ⟨FQ, RQ, hFQ, hRQ⟩ := eQ
  have pubf : finiteDeficiency (publicExperiment p Q) (publicExperiment p P) = ENNReal.ofReal (1/18 : ℝ) := by
    apply le_antisymm
    · exact (transport _ _ _ _ FP RQ hFP hRQ).trans_eq dsf
    · rw [← dsf]
      exact transport _ _ _ _ RP FQ hRP hFQ
  have pubr : finiteDeficiency (publicExperiment p P) (publicExperiment p Q) = ENNReal.ofReal (5/36 : ℝ) := by
    apply le_antisymm
    · exact (transport _ _ _ _ FQ RP hFQ hRP).trans_eq dsr
    · rw [← dsr]
      exact transport _ _ _ _ RQ FP hRQ hFP
  have certificate : Certificate := by
    refine ⟨fun b => ⟨hw b, hv b⟩, hwr, hvr, hH, hJ, htH, htJ, hp, hs,
      rwR, rvR, rwL, rvL, df, dr, violation, necessary, hsm, dsf, dsr, ?_⟩
    refine ⟨p, P, Q, hp0, hp1, hPw, hQv, ⟨FP, RP, hFP, hRP⟩,
      ⟨FQ, RQ, hFQ, hRQ⟩, pubf, pubr, ?_⟩
    rw [hsm, pubf, pubr]; norm_num
  exact fun h => (not_le_of_gt violation) (h certificate)
end
end D5.S3.Estimation.DecisionRisk.CARFourStateReverseObstruction
