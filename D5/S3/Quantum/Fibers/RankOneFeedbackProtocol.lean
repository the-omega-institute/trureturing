/- GID: D5/S3/Quantum/Fibers/RankOneFeedbackProtocol
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/RankOneFeedbackProtocol
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Operational finite rank-one feedback trees reduce to the first complete read. -/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.TotalVariation.DataProcessing
import Mathlib.Data.NNReal.Basic
import D5.S3.TotalVariation.Metric
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators ComplexOrder Matrix

namespace D5.S3.Quantum.Fibers.RankOneFeedbackProtocol

open D5.S3.TotalVariation.Pinsker

universe u
variable {n : Type u} [Fintype n] [DecidableEq n]

/-- A waiting semigroup on the actual complex matrix interface. -/
structure Menu (n : Type*) [Fintype n] [DecidableEq n] where
  wait : NNReal → Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ
  zero : wait 0 = LinearMap.id
  add : ∀ t u X, wait u (wait t X) = wait (t + u) X
  trace : ∀ t X, Matrix.trace (wait t X) = Matrix.trace X
  positive : ∀ t X, X.PosSemidef → (wait t X).PosSemidef

/-- All finite feedback trees, with independent control fixed before the input. -/
inductive Protocol (n : Type*) where
  | stop
  | wait (time : NNReal) (next : Protocol n)
  | read (next : n → Protocol n)

/-- The complete recorded outcomes; Stop before any read has one terminal record. -/
@[reducible] def Record : Protocol n → Type u
  | .stop => PUnit
  | .wait _ P => Record P
  | .read P => (s : n) × Record (P s)

@[reducible] instance recordFintype (P : Protocol n) : Fintype (Record P) := by
  induction P with
  | stop => exact inferInstanceAs (Fintype PUnit)
  | wait t P ih => exact ih
  | read P ih =>
    letI : ∀ s, Fintype (Record (P s)) := ih
    exact inferInstanceAs (Fintype ((s : n) × Record (P s)))

/-- The normalized post-read state is defined even on zero-probability branches. -/
def projector (s : n) : Matrix n n ℂ := Matrix.single s s 1

/-- Unnormalized rank-one branches, evaluated without conditional-probability division. -/
def branch (s : n) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  ((X s s).re : ℂ) • projector s

/-- Operational recursion for terminal record mass. -/
def law (M : Menu n) : (P : Protocol n) → Matrix n n ℂ → Record P → ℝ
  | .stop, X, _ => (Matrix.trace X).re
  | .wait t P, X, h => law M P (M.wait t X) h
  | .read P, X, h => law M (P h.1) (branch h.1 X) h.2

private theorem law_smul (M : Menu n) (P : Protocol n) (X : Matrix n n ℂ)
    (c : ℝ) (h : Record P) : law M P ((c : ℂ) • X) h = c * law M P X h := by
  induction P generalizing X with
  | stop => simp [law, Matrix.trace_smul]
  | wait t P ih => simpa [law] using ih (M.wait t X) h
  | read P ih =>
    have hb : branch h.1 ((c : ℂ) • X) = (c : ℂ) • branch h.1 X := by
      ext i j
      simp [branch, Matrix.smul_apply, smul_eq_mul, mul_assoc]
    simp only [law, hb]
    exact ih h.1 (branch h.1 X) h.2

theorem law_mass (M : Menu n) (P : Protocol n) (X : Matrix n n ℂ) :
    ∑ h : Record P, law M P X h = (Matrix.trace X).re := by
  induction P generalizing X with
  | stop => simp [law, Record]
  | wait t P ih => simpa [law, M.trace] using ih (M.wait t X)
  | read P ih =>
    rw [Fintype.sum_sigma]
    simp only [law]
    simp_rw [ih]
    simp [branch, projector, Matrix.trace_smul, Matrix.trace_single_eq_same,
      Matrix.trace, map_sum]

theorem projector_positive (s : n) : (projector s).PosSemidef := by
  convert Matrix.posSemidef_vecMulVec_self_star (Pi.single s (1 : ℂ)) using 1
  ext i j
  simp [projector, Matrix.vecMulVec, Matrix.single, Pi.single_apply]
  split_ifs <;> simp_all <;> aesop


theorem law_nonnegative (M : Menu n) (P : Protocol n) (X : Matrix n n ℂ)
    (hX : X.PosSemidef) (h : Record P) : 0 ≤ law M P X h := by
  induction P generalizing X with
  | stop =>
    simpa [law] using (Complex.nonneg_iff.mp hX.trace_nonneg).1
  | wait t P ih => exact ih _ (M.positive t X hX) h
  | read P ih =>
    apply ih h.1 _ _ h.2
    exact (projector_positive h.1).smul
      (Complex.nonneg_iff.mpr ⟨(Complex.nonneg_iff.mp hX.diag_nonneg).1, by simp⟩)

/-- Every suffix is a probability law independent of the original density input. -/
def suffix (M : Menu n) (P : n → Protocol n) (s : n) : Record (P s) → ℝ :=
  law M (P s) (projector s)


private theorem suffix_law (M : Menu n) (P : n → Protocol n) (s : n) :
    (∀ h, 0 ≤ suffix M P s h) ∧ ∑ h, suffix M P s h = 1 := by
  exact ⟨fun h => law_nonnegative M (P s) _ (projector_positive s) h,
    by simpa [suffix, projector] using law_mass M (P s) (projector s)⟩

private theorem read_tv (M : Menu n) (P : n → Protocol n) (X Y : Matrix n n ℂ) :
    totalVariation (law M (.read P) X) (law M (.read P) Y) =
      totalVariation (fun s => (X s s).re) (fun s => (Y s s).re) := by
  classical
  unfold totalVariation
  congr 1
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _
  simp only [law, branch]
  simp_rw [law_smul]
  calc
    (∑ h, |(X s s).re * law M (P s) (projector s) h -
        (Y s s).re * law M (P s) (projector s) h|) =
        ∑ h, |(X s s).re - (Y s s).re| * suffix M P s h := by
      apply Finset.sum_congr rfl
      intro h _
      rw [← sub_mul, abs_mul]
      change |(X s s).re - (Y s s).re| * |suffix M P s h| = _
      rw [abs_of_nonneg ((suffix_law M P s).1 h)]
    _ = |(X s s).re - (Y s s).re| := by
      rw [← Finset.mul_sum, (suffix_law M P s).2, mul_one]

/-- An actual protocol either stops without a read or has the exact TV of one first read.
The witness time is the sum of its nonnegative waits before the first outcome. -/
private theorem protocol_first_read_reduction (M : Menu n) (P : Protocol n)
    (X Y : Matrix n n ℂ) (htrace : Matrix.trace X = Matrix.trace Y) :
    totalVariation (law M P X) (law M P Y) = 0 ∨
      ∃ t : NNReal, totalVariation (law M P X) (law M P Y) =
        totalVariation (fun s => ((M.wait t X) s s).re)
          (fun s => ((M.wait t Y) s s).re) := by
  induction P generalizing X Y with
  | stop => left; simp [law, totalVariation, htrace]
  | read P ih =>
    right
    refine ⟨0, ?_⟩
    simpa [M.zero] using read_tv M P X Y
  | wait t P ih =>
    obtain h | ⟨u, hu⟩ := ih (M.wait t X) (M.wait t Y) (by rw [M.trace, M.trace, htrace])
    · exact Or.inl h
    · right
      exact ⟨t + u, by simpa [law, M.add] using hu⟩

/-- The supremum over all finite complete-record feedback trees is the one-read supremum. -/
private theorem finite_protocol_tv_supremum (M : Menu n) (X Y : Matrix n n ℂ)
    (htrace : Matrix.trace X = Matrix.trace Y) :
    sSup (Set.range (fun P : Protocol n => totalVariation (law M P X) (law M P Y))) =
      sSup (Set.range (fun t : NNReal =>
        totalVariation (fun s => ((M.wait t X) s s).re)
          (fun s => ((M.wait t Y) s s).re))) := by
  apply csSup_eq_csSup_of_forall_exists_le
  · rintro _ ⟨P, rfl⟩
    obtain h | ⟨t, ht⟩ := protocol_first_read_reduction M P X Y htrace
    · refine ⟨_, ⟨0, rfl⟩, ?_⟩
      change totalVariation (law M P X) (law M P Y) ≤ _
      rw [h]
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    · exact ⟨_, ⟨t, rfl⟩, le_of_eq ht⟩
  · rintro _ ⟨t, rfl⟩
    refine ⟨_, ⟨.wait t (.read fun _ => .stop), rfl⟩, ?_⟩
    exact le_of_eq (read_tv M (fun _ => .stop) (M.wait t X) (M.wait t Y)).symm

/-- A unitary semigroup supplies the matrix waiting menu without an additional instrument. -/
def unitaryMenu (U : NNReal → Matrix n n ℂ)
    (hzero : U 0 = 1) (hadd : ∀ t u, U (t + u) = U u * U t)
    (hunitary : ∀ t, (U t)ᴴ * U t = 1) : Menu n where
  wait t := {
    toFun := fun X => U t * X * (U t)ᴴ
    map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' := by intro c X; simp }
  zero := by ext X; simp [hzero]
  add := by
    intro t u X
    change U u * (U t * X * (U t)ᴴ) * (U u)ᴴ = U (t+u) * X * (U (t+u))ᴴ
    simp only [hadd, Matrix.conjTranspose_mul, mul_assoc]
  trace := by
    intro t X
    change Matrix.trace (U t * X * (U t)ᴴ) = _
    rw [Matrix.trace_mul_cycle, hunitary, one_mul]
  positive := fun t X hX => hX.mul_mul_conjTranspose_same (U t)

/-- The branch recursion is exactly the rank-one Lueders instrument on Hermitian matrices. -/
private theorem branch_is_lueders (s : n) (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    projector s * X * projector s = branch s X := by
  have he : star (X s s) = X s s := congrFun (congrFun hX s) s
  have hi := congrArg Complex.im he
  have hr : ((X s s).re : ℂ) = X s s := by
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      have : -(X s s).im = (X s s).im := by simpa using hi
      linarith
  rw [branch, hr, projector, Matrix.single_mul_mul_single]
  simp [Matrix.smul_single]

/-- Actual unnormalized Lueders evaluation on every finite retained history. -/
def ludersLaw (M : Menu n) : (P : Protocol n) → Matrix n n ℂ → Record P → ℝ
  | .stop, X, _ => (Matrix.trace X).re
  | .wait t P, X, h => ludersLaw M P (M.wait t X) h
  | .read P, X, h =>
    ludersLaw M (P h.1) (projector h.1 * X * projector h.1) h.2

theorem luders_law_eq (M : Menu n) (P : Protocol n) (X : Matrix n n ℂ)
    (hX : X.PosSemidef) : ludersLaw M P X = law M P X := by
  induction P generalizing X with
  | stop => rfl
  | wait t P ih => exact ih _ (M.positive t X hX)
  | read P ih =>
    funext h
    simp only [ludersLaw, law]
    rw [branch_is_lueders _ _ hX.isHermitian]
    have hp : (branch h.1 X).PosSemidef :=
      (projector_positive h.1).smul
        (Complex.nonneg_iff.mpr ⟨(Complex.nonneg_iff.mp hX.diag_nonneg).1, by simp⟩)
    exact congrFun (ih h.1 _ hp) h.2

/-- The actual unitary-wait, complete rank-one-read, Stop menu has the first-read TV supremum.
Both inputs are arbitrary positive matrices of the same trace; trace-one densities are included. -/
theorem actual_protocol_tv_supremum
    (U : NNReal → Matrix n n ℂ)
    (hzero : U 0 = 1) (hadd : ∀ t u, U (t + u) = U u * U t)
    (hunitary : ∀ t, (U t)ᴴ * U t = 1)
    (X Y : Matrix n n ℂ) (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htrace : Matrix.trace X = Matrix.trace Y) :
    let M := unitaryMenu U hzero hadd hunitary
    sSup (Set.range (fun P : Protocol n =>
      totalVariation (ludersLaw M P X) (ludersLaw M P Y))) =
    sSup (Set.range (fun t : NNReal =>
      totalVariation (fun s => ((U t * X * (U t)ᴴ) s s).re)
        (fun s => ((U t * Y * (U t)ᴴ) s s).re))) := by
  dsimp only
  have hl (P : Protocol n) := luders_law_eq (unitaryMenu U hzero hadd hunitary) P X hX
  have hr (P : Protocol n) := luders_law_eq (unitaryMenu U hzero hadd hunitary) P Y hY
  simp_rw [hl, hr]
  exact finite_protocol_tv_supremum _ X Y htrace

/-- A finite control seed is sampled independently of the unknown input. Its selected
strategy may use all subsequent recorded outcomes. Zero-weight seeds are retained. -/
structure RandomControl (n : Type*) where
  count : ℕ
  weight : Fin count → ℝ
  nonnegative : ∀ c, 0 ≤ weight c
  normalized : ∑ c, weight c = 1
  strategy : Fin count → Protocol n

@[reducible] def RandomRecord (R : RandomControl n) : Type u :=
  (c : Fin R.count) × Record (R.strategy c)

@[reducible] instance randomRecordFintype (R : RandomControl n) : Fintype (RandomRecord R) :=
  inferInstanceAs (Fintype ((c : Fin R.count) × Record (R.strategy c)))

/-- The recorded seed and complete read history form the actual joint mass law. -/
def randomLaw (M : Menu n) (R : RandomControl n) (X : Matrix n n ℂ)
    (h : RandomRecord R) : ℝ :=
  R.weight h.1 * ludersLaw M (R.strategy h.1) X h.2

private theorem random_tv (M : Menu n) (R : RandomControl n) (X Y : Matrix n n ℂ) :
    totalVariation (randomLaw M R X) (randomLaw M R Y) =
      ∑ c, R.weight c * totalVariation (ludersLaw M (R.strategy c) X)
        (ludersLaw M (R.strategy c) Y) := by
  classical
  unfold totalVariation
  simp only [randomLaw]
  rw [Fintype.sum_sigma]
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg (R.nonnegative _)]
  simp only [← Finset.mul_sum, Finset.mul_sum]
  ring

private theorem random_dominated (M : Menu n) (R : RandomControl n)
    (X Y : Matrix n n ℂ) :
    ∃ P : Protocol n, totalVariation (randomLaw M R X) (randomLaw M R Y) ≤
      totalVariation (ludersLaw M P X) (ludersLaw M P Y) := by
  classical
  let f c := totalVariation (ludersLaw M (R.strategy c) X) (ludersLaw M (R.strategy c) Y)
  have hn : (Finset.univ : Finset (Fin R.count)).Nonempty :=
    Finset.nonempty_of_sum_ne_zero (by rw [R.normalized]; norm_num)
  obtain ⟨c, _, hc⟩ := Finset.exists_max_image Finset.univ f hn
  refine ⟨R.strategy c, ?_⟩
  rw [random_tv]
  calc
    ∑ a, R.weight a * f a ≤ ∑ a, R.weight a * f c := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hc a ha) (R.nonnegative a)
    _ = f c := by rw [← Finset.sum_mul, R.normalized, one_mul]

private def fixedControl (P : Protocol n) : RandomControl n where
  count := 1
  weight _ := 1
  nonnegative _ := zero_le_one
  normalized := by simp
  strategy _ := P

/-- Finite independent randomized control has the same supremum, and any finite stochastic
coarse output contracts its complete recorded law. The kernel has no access to the input. -/
theorem randomized_protocol_tv_supremum
    (U : NNReal → Matrix n n ℂ)
    (hzero : U 0 = 1) (hadd : ∀ t u, U (t + u) = U u * U t)
    (hunitary : ∀ t, (U t)ᴴ * U t = 1)
    (X Y : Matrix n n ℂ) (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htrace : Matrix.trace X = Matrix.trace Y) :
    let M := unitaryMenu U hzero hadd hunitary
    (sSup (Set.range (fun R : RandomControl n =>
      totalVariation (randomLaw M R X) (randomLaw M R Y))) =
      sSup (Set.range (fun t : NNReal =>
        totalVariation (fun s => ((U t * X * (U t)ᴴ) s s).re)
          (fun s => ((U t * Y * (U t)ᴴ) s s).re)))) ∧
    (∀ (R : RandomControl n) (m : ℕ) (W : RandomRecord R → Fin m → ℝ),
      ((∀ h j, 0 ≤ W h j) ∧ (∀ h, ∑ j, W h j = 1)) →
      totalVariation (D5.S3.Divergence.ClassicalDPI.channelOutput W (randomLaw M R X))
        (D5.S3.Divergence.ClassicalDPI.channelOutput W (randomLaw M R Y)) ≤
          totalVariation (randomLaw M R X) (randomLaw M R Y)) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [← actual_protocol_tv_supremum U hzero hadd hunitary X Y hX hY htrace]
    apply csSup_eq_csSup_of_forall_exists_le
    · rintro _ ⟨R, rfl⟩
      obtain ⟨P, hP⟩ := random_dominated (unitaryMenu U hzero hadd hunitary) R X Y
      exact ⟨_, ⟨P, rfl⟩, hP⟩
    · rintro _ ⟨P, rfl⟩
      refine ⟨_, ⟨fixedControl P, rfl⟩, ?_⟩
      simp [random_tv, fixedControl]
  · intro R m W hW
    exact D5.S3.TotalVariation.DataProcessing.total_variation_channel_le _ _ W hW

/-- The actual Heisenberg effect of one complete recorded Lueders history. -/
def recordEffect (U : NNReal → Matrix n n ℂ) : (P : Protocol n) → Record P → Matrix n n ℂ
  | .stop, _ => 1
  | .wait t P, h => (U t)ᴴ * recordEffect U P h * U t
  | .read P, h => projector h.1 * recordEffect U (P h.1) h.2 * projector h.1

/-- One wait followed by one specified mode outcome. -/
def firstEffect (U : NNReal → Matrix n n ℂ) (t : NNReal) (s : n) : Matrix n n ℂ :=
  (U t)ᴴ * projector s * U t

private theorem recordEffect_hermitian (U : NNReal → Matrix n n ℂ)
    (P : Protocol n) (h : Record P) : (recordEffect U P h).IsHermitian := by
  induction P with
  | stop => exact Matrix.isHermitian_one
  | wait t P ih => exact Matrix.isHermitian_conjTranspose_mul_mul (U t) (ih h)
  | read P ih =>
    have hs : (projector h.1)ᴴ = projector h.1 := (projector_positive h.1).isHermitian
    simpa only [recordEffect, hs] using
      Matrix.isHermitian_conjTranspose_mul_mul (projector h.1) (ih h.1 h.2)

private theorem recordEffect_probability (U : NNReal → Matrix n n ℂ)
    (hzero : U 0 = 1) (hadd : ∀ t u, U (t+u) = U u * U t)
    (hunitary : ∀ t, (U t)ᴴ * U t = 1)
    (P : Protocol n) (X : Matrix n n ℂ) (h : Record P) :
    (Matrix.trace (recordEffect U P h * X)).re =
      ludersLaw (unitaryMenu U hzero hadd hunitary) P X h := by
  induction P generalizing X with
  | stop => simp [recordEffect, ludersLaw]
  | wait t P ih =>
    change (Matrix.trace ((U t)ᴴ * recordEffect U P h * U t * X)).re = _
    have ht : Matrix.trace ((U t)ᴴ * recordEffect U P h * U t * X) =
        Matrix.trace (recordEffect U P h * (U t * X * (U t)ᴴ)) := by
      simp only [mul_assoc]
      rw [Matrix.trace_mul_comm (U t)ᴴ]
      simp only [mul_assoc]
    rw [ht]
    simpa only [ludersLaw, unitaryMenu, LinearMap.coe_mk, AddHom.coe_mk] using
      ih (U t * X * (U t)ᴴ) h
  | read P ih =>
    change (Matrix.trace (projector h.1 * recordEffect U (P h.1) h.2 * projector h.1 * X)).re = _
    have ht : Matrix.trace (projector h.1 * recordEffect U (P h.1) h.2 * projector h.1 * X) =
        Matrix.trace (recordEffect U (P h.1) h.2 * (projector h.1 * X * projector h.1)) := by
      simp only [mul_assoc]
      rw [Matrix.trace_mul_comm (projector h.1)]
      simp only [mul_assoc]
    rw [ht]
    simpa only [ludersLaw] using
      ih h.1 (projector h.1 * X * projector h.1) h.2

/-- The real linear observation space supplied by Stop and the actual one-read family. -/
def firstEffectSpan (U : NNReal → Matrix n n ℂ) : Submodule ℝ (Matrix n n ℂ) :=
  Submodule.span ℝ (insert 1 (Set.range (fun p : NNReal × n => firstEffect U p.1 p.2)))

private theorem waiting_preserves_span (U : NNReal → Matrix n n ℂ)
    (hadd : ∀ t u, U (t+u) = U u * U t) (hunitary : ∀ t, (U t)ᴴ * U t = 1)
    (t : NNReal) (E : Matrix n n ℂ) (hE : E ∈ firstEffectSpan U) :
    (U t)ᴴ * E * U t ∈ firstEffectSpan U := by
  induction hE using Submodule.span_induction with
  | mem E hE =>
    obtain rfl | ⟨⟨u,s⟩, rfl⟩ := hE
    · rw [mul_one, hunitary]
      exact Submodule.subset_span (Set.mem_insert 1 _)
    · have he : (U t)ᴴ * firstEffect U u s * U t = firstEffect U (t+u) s := by
        simp [firstEffect, hadd, Matrix.conjTranspose_mul, mul_assoc]
      rw [he]
      exact Submodule.subset_span (Set.mem_insert_of_mem 1 ⟨(t+u,s), rfl⟩)
  | zero => simp
  | add E F _ _ hE hF => simpa only [Matrix.mul_add, Matrix.add_mul] using
      (firstEffectSpan U).add_mem hE hF
  | smul c E _ hE => simpa using (firstEffectSpan U).smul_mem c hE

private theorem projector_complement_positive (s : n) :
    (1 - projector s).PosSemidef := by
  have he : 1 - projector s = Matrix.diagonal (fun i => if i = s then (0 : ℂ) else 1) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases his : i = s
      · subst i; simp [projector, Matrix.single, Matrix.diagonal]
      · simp [projector, Matrix.single, Matrix.diagonal, his, Ne.symm his]
    · simp [projector, Matrix.single, Matrix.diagonal, Matrix.one_apply, hij]
      aesop
  rw [he]
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ if i = s then 0 else 1
  split_ifs <;> simp

private theorem recordEffect_bounds (U : NNReal → Matrix n n ℂ)
    (hunitary : ∀ t, (U t)ᴴ * U t = 1) (P : Protocol n) (h : Record P) :
    (recordEffect U P h).PosSemidef ∧ (1 - recordEffect U P h).PosSemidef := by
  induction P with
  | stop => simpa [recordEffect] using
      (show (1 : Matrix n n ℂ).PosSemidef ∧ (0 : Matrix n n ℂ).PosSemidef from
        ⟨Matrix.PosSemidef.one, Matrix.PosSemidef.zero⟩)
  | wait t P ih =>
    refine ⟨(ih h).1.conjTranspose_mul_mul_same (U t), ?_⟩
    have he : 1 - (U t)ᴴ * recordEffect U P h * U t =
        (U t)ᴴ * (1 - recordEffect U P h) * U t := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, mul_one, hunitary t]
    rw [recordEffect, he]
    exact (ih h).2.conjTranspose_mul_mul_same (U t)
  | read P ih =>
    have hs : (projector h.1)ᴴ = projector h.1 := (projector_positive h.1).isHermitian.eq
    have hi : projector h.1 * projector h.1 = projector h.1 := by
      simp [projector, Matrix.single_mul_single_same]
    refine ⟨by simpa only [recordEffect, hs] using
      (ih h.1 h.2).1.conjTranspose_mul_mul_same (projector h.1), ?_⟩
    have he : 1 - projector h.1 * recordEffect U (P h.1) h.2 * projector h.1 =
        (1 - projector h.1) +
          (projector h.1)ᴴ * (1 - recordEffect U (P h.1) h.2) * projector h.1 := by
      simp only [hs, Matrix.mul_sub, Matrix.sub_mul, mul_one, hi]
      abel
    rw [recordEffect, he]
    exact (projector_complement_positive h.1).add
      ((ih h.1 h.2).2.conjTranspose_mul_mul_same (projector h.1))

/-- All actual finite protocol effects have precisely the Stop-plus-single-read span.
The probability identity ties the suppliers to the actual complex Lueders instrument. -/
theorem actual_protocol_effect_correspondence
    (U : NNReal → Matrix n n ℂ)
    (hzero : U 0 = 1) (hadd : ∀ t u, U (t+u) = U u * U t)
    (hunitary : ∀ t, (U t)ᴴ * U t = 1) :
    (Submodule.span ℝ (Set.range (fun p : (P : Protocol n) × Record P =>
      recordEffect U p.1 p.2)) = firstEffectSpan U) ∧
    (∀ (P : Protocol n) (X : Matrix n n ℂ) (h : Record P),
      (Matrix.trace (recordEffect U P h * X)).re =
        ludersLaw (unitaryMenu U hzero hadd hunitary) P X h) ∧
    (∀ (P : Protocol n) (h : Record P),
      (recordEffect U P h).PosSemidef ∧ (1 - recordEffect U P h).PosSemidef) := by
  refine ⟨?_, recordEffect_probability U hzero hadd hunitary, recordEffect_bounds U hunitary⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨P,h⟩, rfl⟩
    induction P with
    | stop => exact Submodule.subset_span (Set.mem_insert 1 _)
    | wait t P ih => exact waiting_preserves_span U hadd hunitary t _ (ih h)
    | read P ih =>
      change projector h.1 * recordEffect U (P h.1) h.2 * projector h.1 ∈ _
      rw [branch_is_lueders _ _ (recordEffect_hermitian U (P h.1) h.2)]
      change (((recordEffect U (P h.1) h.2) h.1 h.1).re : ℂ) • projector h.1 ∈ _
      change ((recordEffect U (P h.1) h.2) h.1 h.1).re • projector h.1 ∈ _
      apply (firstEffectSpan U).smul_mem
      have he : projector h.1 = firstEffect U 0 h.1 := by simp [firstEffect, hzero]
      rw [he]
      exact Submodule.subset_span (Set.mem_insert_of_mem 1 ⟨(0,h.1), rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ (rfl | ⟨⟨t,s⟩, rfl⟩)
    · exact Submodule.subset_span ⟨⟨.stop, PUnit.unit⟩, rfl⟩
    · refine Submodule.subset_span ⟨⟨.wait t (.read fun _ => .stop), ⟨s,PUnit.unit⟩⟩, ?_⟩
      simp [recordEffect, firstEffect, projector, Matrix.single_mul_single_same]

/-- The accessible first-read distinction supremum. -/
def firstSup (M : Menu n) (X Y : Matrix n n ℂ) : ℝ :=
  sSup (Set.range (fun t : NNReal => totalVariation
    (fun s => ((M.wait t X) s s).re) (fun s => ((M.wait t Y) s s).re)))

private theorem first_sup_bounded (M : Menu n) (X Y : Matrix n n ℂ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htX : Matrix.trace X = 1) (htY : Matrix.trace Y = 1) :
    BddAbove (Set.range (fun t : NNReal => totalVariation
      (fun s => ((M.wait t X) s s).re) (fun s => ((M.wait t Y) s s).re))) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨t,rfl⟩
  apply D5.S3.TotalVariation.Metric.total_variation_le_one
  · refine ⟨fun s => (Complex.nonneg_iff.mp (M.positive t X hX).diag_nonneg).1, ?_⟩
    simpa [Matrix.trace] using congrArg Complex.re ((M.trace t X).trans htX)
  · refine ⟨fun s => (Complex.nonneg_iff.mp (M.positive t Y hY).diag_nonneg).1, ?_⟩
    simpa [Matrix.trace] using congrArg Complex.re ((M.trace t Y).trans htY)

private theorem protocol_le_first_sup (M : Menu n) (P : Protocol n) (X Y : Matrix n n ℂ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htX : Matrix.trace X = 1) (htY : Matrix.trace Y = 1) :
    totalVariation (ludersLaw M P X) (ludersLaw M P Y) ≤ firstSup M X Y := by
  rw [luders_law_eq M P X hX, luders_law_eq M P Y hY]
  have hb := first_sup_bounded M X Y hX hY htX htY
  obtain h | ⟨t,ht⟩ := protocol_first_read_reduction M P X Y (htX.trans htY.symm)
  · rw [h]
    exact (D5.S3.TotalVariation.Metric.total_variation_nonneg _ _).trans
      (le_csSup hb ⟨0,rfl⟩)
  · rw [ht]
    exact le_csSup hb ⟨t,rfl⟩

/-- Arbitrary independent probability seeds cannot improve any legal recorded event gap.
The seed can select a finite feedback tree with arbitrary real waiting times. Integrability
is the explicit measurability requirement for the two actual event probabilities. -/
theorem arbitrary_random_control_event_bound
    (U : NNReal → Matrix n n ℂ)
    (hzero : U 0 = 1) (hadd : ∀ t u, U (t + u) = U u * U t)
    (hunitary : ∀ t, (U t)ᴴ * U t = 1)
    (X Y : Matrix n n ℂ) (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htX : Matrix.trace X = 1) (htY : Matrix.trace Y = 1)
    {Seed : Type*} [MeasurableSpace Seed] (μ : MeasureTheory.Measure Seed)
    [MeasureTheory.IsProbabilityMeasure μ]
    (strategy : Seed → Protocol n) (event : ∀ c, Finset (Record (strategy c)))
    (hp : MeasureTheory.Integrable
      (fun c => ∑ h ∈ event c, ludersLaw (unitaryMenu U hzero hadd hunitary) (strategy c) X h) μ)
    (hq : MeasureTheory.Integrable
      (fun c => ∑ h ∈ event c, ludersLaw (unitaryMenu U hzero hadd hunitary) (strategy c) Y h) μ) :
    |(∫ c, ∑ h ∈ event c, ludersLaw (unitaryMenu U hzero hadd hunitary) (strategy c) X h ∂μ) -
      (∫ c, ∑ h ∈ event c, ludersLaw (unitaryMenu U hzero hadd hunitary) (strategy c) Y h ∂μ)| ≤
      firstSup (unitaryMenu U hzero hadd hunitary) X Y := by
  classical
  let M := unitaryMenu U hzero hadd hunitary
  have he (c : Seed) :
      |(∑ h ∈ event c, ludersLaw M (strategy c) X h) -
        (∑ h ∈ event c, ludersLaw M (strategy c) Y h)| ≤ firstSup M X Y := by
    have hm : ∑ h, ludersLaw M (strategy c) X h = ∑ h, ludersLaw M (strategy c) Y h := by
      rw [luders_law_eq M _ X hX, luders_law_eq M _ Y hY, law_mass, law_mass, htX, htY]
    exact ((D5.S3.TotalVariation.Metric.total_variation_eq_sup_event_gap _ _ hm).2
      ⟨event c, rfl⟩).trans (protocol_le_first_sup M (strategy c) X Y hX hY htX htY)
  rw [← MeasureTheory.integral_sub hp hq]
  calc
    _ ≤ ∫ c, |(∑ h ∈ event c, ludersLaw M (strategy c) X h) -
        (∑ h ∈ event c, ludersLaw M (strategy c) Y h)| ∂μ :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _ : Seed, firstSup M X Y ∂μ :=
      MeasureTheory.integral_mono (hp.sub hq).abs (MeasureTheory.integrable_const _) he
    _ = firstSup M X Y := by simp

end D5.S3.Quantum.Fibers.RankOneFeedbackProtocol
