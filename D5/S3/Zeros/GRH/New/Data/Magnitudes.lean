/- GID: D5/S3/Zeros/GRH/New/Data/Magnitudes
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Data/Magnitudes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Data.Magnitudes. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Data/Magnitudes.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Data.AdmissibleData
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: size bookkeeping for the data of this proof.

This file: Logarithmic size calculus (upper and lower exponent bounds) for the parameters of the
data. -/

noncomputable section

open Real Set Finset Nat NeZero

namespace Data

variable {P} (D : Data P) {F G l l' c : ℝ} {A B : ℕ} {u}

/-- A bound on the size of the real F on a logarithmic scale: |F| ≤ exp(l) if u is true, and
exp(l) ≤ F if u is false. -/
class HasLogBound (D : Data P) (u : Bool) F (l :
  outParam ℝ) where out : ite u (|F| ≤ exp l) (exp l ≤ F)

lemma c_ge : 64 ≤ P.c ∧ P.N₀ ≤ P.c ∧ P.d ≤ P.c ∧ φ P.N₀ ≤ P.c := by
  grw [totient_le]; grind [Parameters.c, sum_nonneg, ofNat_lt_cast, P.lt_d]

attribute [local grind!] HasLogBound NeZero exp_pos exp_log exp_zero add_one_le_exp inv_anti₀
  one_le_cast ceil_lt_add_one le_ceil ceil_eq_zero s_le log_mul

lemma r_odd : Odd D.r := by grind [D.r_pow]

/-- The number m of the data is even. -/
lemma m_even : Even D.m := by grind [D.m_pow]

attribute [grind! .] c_ge r_odd m_even

lemma placeClass_of_thick : ∀ σ ∈ D.thick, P.placeClass ⟨_, rfl⟩ σ = -1 :=
  D.thick_eq_neg_one_mod _ ⟨_, rfl⟩

/-- For reals F and l, the statement that |F| ≤ exp(l). -/
abbrev HasLogUpper := D.HasLogBound true

/-- For reals F and l, the statement that exp(l) ≤ F. -/
abbrev HasLogLower := D.HasLogBound false

lemma HasLogBound.pos [D.HasLogLower F l] : 0 < F := by grind

section

variable {D} [HasLogBound D u F l] [HasLogBound D u G l']

lemma HasLogBound.of_mem_Icc {l} (G H := F) [D.HasLogLower G l] [D.HasLogUpper H l'] (e :
  F ∈ Icc G H := by simp) (a : ite u (l' ≤ c)
  (c ≤ l) := by cases u <;> grind [D.scale]) : HasLogBound D u F c := by grind [=_ exp_le_exp]

instance (priority := low) hasLogBound_natCast [NeZero A] :
  HasLogBound D u A (ite u A 0) := by grind

instance (priority := low) [A.AtLeastTwo] : HasLogBound D u ofNat(A) (ite u ofNat(A) 0) :=
  hasLogBound_natCast

instance : HasLogBound D u 1 0 := by grind

instance : HasLogBound D u c.exp c := by grind

instance hasLogBound_mul : HasLogBound D u (F * G) (l + l') := by grind [exp_add, mul_le_mul]

instance hasLogBound_add : HasLogBound D u (F + G) (max l l' + ite u 1 0) := ⟨by
  split; grw [exp_add, ← exp_one_gt_two, exp_monotone.map_max]; repeat grind⟩

instance [D.HasLogLower F l] : D.HasLogUpper F⁻¹ (-l) := by grind [exp_neg]

instance [D.HasLogUpper F l] [D.HasLogLower F l'] : D.HasLogLower F⁻¹ (-l) := by grind [exp_neg]

instance [HasLogBound D u G⁻¹ l'] : HasLogBound D u (F / G) (l + l') := hasLogBound_mul

instance : HasLogBound D u (F ^ A) (A * l) := by grind [exp_nat_mul, pow_le_pow_left₀]

instance : HasLogBound D u √F (l / 2) := by grind [exp_half, abs_le_sqrt, Real.le_sqrt]

instance [HasLogBound D u (A * B) l] : HasLogBound D u ↑(A * B) l := by simpa

instance [HasLogBound D u (A + B) l] : HasLogBound D u ↑(A + B) l := by simpa

instance [HasLogBound D u (A ^ B) l] : HasLogBound D u ↑(A ^ B) l := by simpa

instance [D.HasLogUpper (|F| + 1) c] : HasLogBound D u ⌈F⌉₊ (ite u c l) := by grind

instance : HasLogBound D u D.logB D.logB.log := by grind [D.scale]

instance : HasLogBound D u D.logX₁ D.logX₁.log := by grind [D.scale]

instance : D.HasLogUpper D.s D.logX₁.log := by grind [D.scale]

variable [D.HasLogUpper F l]

lemma hasLogUpper_of_abs_le : |G| ≤ F → D.HasLogUpper G l := by grind

lemma hasLogUpper_of_le_of_nonneg (e : G ≤ F) (h : 0 ≤ G := by positivity) :
  D.HasLogUpper G l := by grind

instance : D.HasLogUpper |F| l := by grind

instance [D.HasLogUpper G l'] : D.HasLogUpper (F - G) (max l l' + 1) :=
  hasLogUpper_of_abs_le (abs_sub ..)

instance (priority := low) [D.HasLogLower F l'] :
  D.HasLogUpper F.log (max (99 + D.logB.log) (max l (-l') - 99 *
  D.logB) + 1) := hasLogUpper_of_abs_le (F := 99 * D.logB + exp _) (by grind [exp_le_exp])

variable (D) [D.HasLogUpper A l] [D.HasLogLower G l'] [D.HasLogLower B l']
  (e : l < l' := by clear_aux_decl; clear * - D; (repeat clear ‹_›); grind (splits := 99) [D.scale])

lemma hasLogUpper_of_le : B ≤ A → D.HasLogUpper B l := by grind [cast_le]

lemma hasLogLower_of_le : G ≤ F → D.HasLogLower F l' := by grind

include D e

protected lemma lt_of_hasLogBound : F < G := by grind [=_ exp_lt_exp]

/-- If |F| ≤ exp l, exp l' ≤ G and l < l', then F ≤ G. The exponents are found by instance search,
and l < l' is by default proved from the scale conditions of the data. -/
protected lemma le_of_hasLogBound : F ≤ G := (D.lt_of_hasLogBound e).le

lemma nat_lt_of_hasLogBound : A < B := cast_lt.1 (D.lt_of_hasLogBound e)

lemma nat_le_of_hasLogBound : A ≤ B := (D.nat_lt_of_hasLogBound e).le

end

instance : HasLogBound D u π (ite u 4 0) := by grind [two_le_pi, pi_le_four]

instance : HasLogBound D u D.m (D.logX / 2 + ite u 2 0) := .of_mem_Icc _ _ D.m_mem

instance : HasLogBound D u D.r (5 * D.logX + ite u 3 0) := .of_mem_Icc _ _ D.r_mem

instance : D.HasLogUpper P.c D.logB.log := by grind [scale]

lemma le_m : 10000 ≤ D.m := D.nat_le_of_hasLogBound

@[grind! .] lemma r_add : D.r + 1 = D.k + D.m := (Nat.sub_add_cancel D.nat_le_of_hasLogBound).symm

lemma k_le_r : D.k ≤ D.r := by grind [le_m]

instance : HasLogBound D u D.k (5 * D.logX + ite u 3 (-2)) := .of_mem_Icc (D.r / 2) D.r
  (by grind [le_m, k, cast_sub, (D.le_of_hasLogBound : D.m ≤ (D.r / 2 : ℝ))])

instance : HasLogBound D u D.t (5 * D.logX + ite u 8 0) := t.eq_1 D ▸ .of_mem_Icc

instance [HasLogBound D u (D.m ^ 22) l] :
  HasLogBound D u (ofNat(2) ^ D.s) l := by cases D.m_pow; simp_all [pow_mul]

instance : HasLogBound D u (towerDeg D.s) (11 * D.logX + ite u (D.logB.log / 5) 0) := by
  have := D.hasLogUpper_of_le (pow_log_le_add_one 3 D.s); rw [towerDeg, pow_add]; exact .of_mem_Icc

/-- `x¹¹ ≤ f ≤ e^c x¹¹ (log b)^{1/5}`. -/
instance hasLogBound_f : HasLogBound D u D.f (11 * D.logX + ite u (D.logB.log / 5 + P.c) 0) :=
  f.eq_1 D ▸ P.card_infinitePlace_E _ ▸ .of_mem_Icc

instance {S : Finset D.Φ} [D.HasLogUpper D.f l] : D.HasLogUpper #S l :=
  D.hasLogUpper_of_le (card_le_univ _)

instance : HasLogBound D u (D.n D.m) (5.5 * D.logX + ite u 12 0) := n.eq_1 .. ▸ .of_mem_Icc

instance (i) : HasLogBound D u (D.g i) (ite u 11 10 * D.logB) := .of_mem_Icc _ _ (g_mem ..)

instance : HasLogBound D u D.gProd (ite u 22 20 * D.logB) := gProd.eq_1 D ▸ .of_mem_Icc

/-- If the real number F satisfies exp(l) ≤ F for some real l, so that F > 0, then the rounded
value N₁⌈F/N₁⌉ (`Data.roundUp`) lies in the closed interval [F, F + N₁]. -/
lemma roundUp_mem_Icc [D.HasLogLower F l] : ↑(D.roundUp F) ∈ Icc F (F + D.N₁) := by
  simp [roundUp]; grw [ceil_lt_add_one (HasLogBound.pos D).le, ← le_ceil]
  simp [mul_add, mul_div_cancel₀, ne]

instance : HasLogBound D u D.h₂ (40 * D.logX + ite u 25 0) := h₂.eq_1 D ▸ .of_mem_Icc

instance : HasLogBound D u D.h (40 * D.logX + ite u 27 0) := h.eq_1 D ▸ .of_mem_Icc

instance : HasLogBound D u D.a (D.logB + D.logX + ite u 1 0) := .of_mem_Icc _ _ D.roundUp_mem_Icc

instance : HasLogBound D u D.b₁ (D.logB + ite u 2 (-2)) := .of_mem_Icc _ _ D.roundUp_mem_Icc

instance : HasLogBound D u D.b₂ (D.logB - D.logX₁ + D.logX + ite u 2 0) :=
  .of_mem_Icc _ _ D.roundUp_mem_Icc

instance {κ S} {v : κ → ℝ} [D.HasLogUpper #S l] [g : ∀ y, D.HasLogUpper (v y) l'] :
  D.HasLogUpper (∑ y ∈ S, v y) (l + l') :=
  hasLogUpper_of_abs_le (by simpa using norm_sum_le_of_le S (f := v) fun y _ ↦ (g y).1)

instance [D.HasLogUpper (|log F| + |log G|) l] : D.HasLogUpper (F * G).log l := by grind

instance [D.HasLogUpper (A * log F) l] : D.HasLogUpper (F ^ A).log l := by simpa

instance [D.HasLogUpper (A * .log A) l] : D.HasLogUpper (log A !) l :=
  hasLogUpper_of_le_of_nonneg (by grw [factorial_le_pow, cast_pow])

lemma hundred_mul_m_le_k : 100 * D.m ≤ D.k := D.nat_le_of_hasLogBound

@[simp] lemma k_pos : 0 < D.k := D.nat_le_of_hasLogBound

lemma n_mono : Monotone D.n := mul_left_mono.const_add _

lemma k_even : Even D.k := by grind

attribute [grind] t h w

lemma t_odd : Odd D.t := by grind

lemma r_add_six_le_t : D.r + 6 ≤ D.t := by grind [D.r_pow]

/-- The number k + t + 1 is at most the half-gap h₂ = r⁸. -/
lemma k_add_t_add_one_le_h₂ : D.k + D.t + 1 ≤ D.h₂ := D.nat_le_of_hasLogBound

attribute [grind! .] k_add_t_add_one_le_h₂ k_pos hundred_mul_m_le_k k_even t_odd k_le_r
  r_add_six_le_t
