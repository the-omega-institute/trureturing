/- GID: D5/S3/Quantum/Foundation/EffectProbabilityExtension
   generality: I
   mirror-B: D5/B/S3/Quantum/Foundation/EffectProbabilityExtension
   mirror-E: none(waiver:finite-dimensional-algebraic-proof)
   anchors: []
   utility: none
   digest: Finite effect additivity yields a positive linear extension and its unique density representative. -/

/-
The probability function is defined on all matrices; only its restriction to positive
contractions occurs in the hypotheses and conclusion. A single effect function supplies
noncontextuality. No continuity, scalar homogeneity or countable additivity is assumed.

The construction follows Busch's effect-probability representation. Its non-normalizing
step extends finite additivity through rational and real scales to the entire positive
cone. This extension is consumed by the Hermitian difference construction, complexification,
and the density representative. The result supplies the converse probability interface
used by the AURIC Omega instrument synthesis; it is not a claim of literature novelty.

proof_shape: effect_real_homogeneity, effect_cone_extension, effect_linear_extension,
effect_density_representation: content.
proof_shape: pairing, effect_trace_unique: bind-only; consumer: effect_density_representation.
The public trace-dual positivity and dual pairing are reused from the existing
PositiveFilterTransposeRefutation owner. The generality tag follows that import.
-/

import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder Kronecker CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteKrausChannel
namespace D5.S3.Quantum.Foundation.EffectProbabilityExtension

private def pairing {d : Type*} [Fintype d] (ρ : Matrix d d ℂ) :
    CStarMatrix d d ℂ →ₗ[ℂ] ℂ where
  toFun E := Matrix.trace (ρ * CStarMatrix.ofMatrix.symm E)
  map_add' E F := by
    change Matrix.trace (ρ * (CStarMatrix.ofMatrix.symm E + CStarMatrix.ofMatrix.symm F)) = _
    simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c E := by
    change Matrix.trace (ρ * (c • CStarMatrix.ofMatrix.symm E)) = _
    simp [Matrix.mul_smul, Matrix.trace_smul]

theorem effect_trace_unique {d : Type*} [Fintype d] [DecidableEq d] (ρ σ : Matrix d d ℂ)
    (h : ∀ E : CStarMatrix d d ℂ, 0 ≤ E → E ≤ 1 → pairing ρ E = pairing σ E) : ρ = σ := by
  have heq : pairing ρ = pairing σ := by
    apply LinearMap.ext_on CStarAlgebra.span_nonneg_inter_unitClosedBall
    intro E hE
    exact h E hE.1 ((CStarAlgebra.norm_le_one_iff_of_nonneg E hE.1).1
      (by simpa using hE.2))
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  exact congrArg (fun F => F (CStarMatrix.ofMatrix X)) heq

private theorem effect_real_homogeneity {d : Type*} [Fintype d] [DecidableEq d]
    (p : CStarMatrix d d ℂ → ℝ)
    (hpos : ∀ E, 0 ≤ E → E ≤ 1 → 0 ≤ p E)
    (hadd : ∀ E F, 0 ≤ E → 0 ≤ F → E + F ≤ 1 → p (E + F) = p E + p F)
    (E : CStarMatrix d d ℂ) (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : p (t • E) = t * p E := by
  have hzero : p 0 = 0 := by
    have h := hadd 0 0 le_rfl le_rfl (by simp)
    simp only [add_zero] at h
    linarith
  have mono (A B : CStarMatrix d d ℂ) (hA : 0 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1) :
      p A ≤ p B := by
    have hd0 : 0 ≤ B - A := sub_nonneg.mpr hAB
    have hd1 : B - A ≤ 1 := (sub_le_self B hA).trans hB
    have hab : A + (B - A) = B := by abel
    have ha := hadd A (B - A) hA hd0 (by rwa [hab])
    rw [hab] at ha
    linarith [hpos (B-A) hd0 hd1]
  have rep (n : ℕ) (F : CStarMatrix d d ℂ) (hF : 0 ≤ F)
      (hbound : n • F ≤ 1) : p (n • F) = (n : ℝ) * p F := by
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
      have hn : n • F ≤ 1 := (le_add_of_nonneg_right hF).trans
        (by simpa only [succ_nsmul] using hbound)
      rw [succ_nsmul, hadd _ _ (nsmul_nonneg hF n) hF
        (by simpa only [succ_nsmul] using hbound), ih hn]
      push_cast
      ring
  have fraction (m n : ℕ) (hn : n ≠ 0) (hmn : m ≤ n) :
      p (((m : ℝ) / n) • E) = ((m : ℝ) / n) * p E := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    let F : CStarMatrix d d ℂ := (n : ℝ)⁻¹ • E
    have hF : 0 ≤ F := smul_nonneg (inv_nonneg.mpr hnR.le) hE0
    have hscale : n • F = E := by
      change n • ((n : ℝ)⁻¹ • E) = E
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ (ne_of_gt hnR), one_smul]
    have hpF := rep n F hF (by rw [hscale]; exact hE1)
    rw [hscale] at hpF
    have hmE : m • F = ((m : ℝ) / n) • E := by
      change m • ((n : ℝ)⁻¹ • E) = _
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, div_eq_mul_inv]
    have hmub : (m : ℝ) / n ≤ 1 := (div_le_one hnR).2 (by exact_mod_cast hmn)
    have hmB : m • F ≤ 1 := by
      rw [hmE]
      exact (smul_le_smul_of_nonneg_right hmub hE0).trans (by simpa using hE1)
    have hpm := rep m F hF hmB
    rw [hmE] at hpm
    rw [hpm, hpF]
    field_simp [ne_of_gt hnR]
    <;> ring
  have rat (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
      p ((q : ℝ) • E) = (q : ℝ) * p E := by
    have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
    have hcast : ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) := by
      rw [Rat.cast_def]
      congr 1
      exact_mod_cast Int.toNat_of_nonneg hnum
    have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hmn : q.num.toNat ≤ q.den := by
      have h := (div_le_one hden).1 (hcast.trans_le (by exact_mod_cast hq1))
      exact_mod_cast h
    simpa only [hcast] using fraction q.num.toNat q.den (Nat.ne_of_gt q.den_pos) hmn
  have htE : t • E ≤ 1 :=
    (smul_le_smul_of_nonneg_right ht1 hE0).trans (by simpa using hE1)
  have hp0 := hpos E hE0 hE1
  have hpt0 := hpos (t • E) (smul_nonneg ht0 hE0) htE
  have hpt1 : p (t • E) ≤ p E :=
    mono _ _ (smul_nonneg ht0 hE0) (by simpa using smul_le_smul_of_nonneg_right ht1 hE0) hE1
  by_cases hpz : p E = 0
  · nlinarith
  have hp : 0 < p E := lt_of_le_of_ne hp0 (Ne.symm hpz)
  have hratio0 : 0 ≤ p (t • E) / p E := div_nonneg hpt0 hp.le
  have hratio1 : p (t • E) / p E ≤ 1 := (div_le_one hp).2 hpt1
  apply le_antisymm
  · by_contra h
    have hlt : t < p (t • E) / p E := (lt_div_iff₀ hp).2 (lt_of_not_ge h)
    obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn hlt
    have hq0 : 0 ≤ q := by exact_mod_cast (ht0.trans hqlo.le)
    have hq1 : q ≤ 1 := by exact_mod_cast (hqhi.le.trans hratio1)
    have hm := mono (t • E) ((q : ℝ) • E) (smul_nonneg ht0 hE0)
      (smul_le_smul_of_nonneg_right hqlo.le hE0)
      ((smul_le_smul_of_nonneg_right (show (q : ℝ) ≤ 1 by exact_mod_cast hq1) hE0).trans (by simpa using hE1))
    rw [rat q hq0 hq1] at hm
    have hh := (lt_div_iff₀ hp).1 hqhi
    linarith
  · by_contra h
    have hlt : p (t • E) / p E < t := (div_lt_iff₀ hp).2 (lt_of_not_ge h)
    obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn hlt
    have hq0 : 0 ≤ q := by exact_mod_cast (hratio0.trans hqlo.le)
    have hq1 : q ≤ 1 := by exact_mod_cast (hqhi.le.trans ht1)
    have hm := mono ((q : ℝ) • E) (t • E)
      (smul_nonneg (by exact_mod_cast hq0) hE0)
      (smul_le_smul_of_nonneg_right hqhi.le hE0) htE
    rw [rat q hq0 hq1] at hm
    have hh := (div_lt_iff₀ hp).1 hqlo
    linarith
#print axioms effect_real_homogeneity

private theorem effect_cone_extension {d : Type*} [Fintype d] [DecidableEq d]
    (p : CStarMatrix d d ℂ → ℝ)
    (hpos : ∀ E, 0 ≤ E → E ≤ 1 → 0 ≤ p E)
    (hadd : ∀ E F, 0 ≤ E → 0 ≤ F → E + F ≤ 1 → p (E + F) = p E + p F) :
    ∃ f : CStarMatrix d d ℂ → ℝ,
      (∀ E, 0 ≤ E → E ≤ 1 → f E = p E) ∧
      (∀ X, 0 ≤ X → 0 ≤ f X) ∧
      (∀ X Y, 0 ≤ X → 0 ≤ Y → f (X+Y) = f X + f Y) ∧
      (∀ X t, 0 ≤ X → 0 ≤ t → f (t • X) = t * f X) := by
  let scale (X : CStarMatrix d d ℂ) : ℝ := ‖X‖ + 1
  have scale_pos (X : CStarMatrix d d ℂ) : 0 < scale X := by dsimp [scale]; positivity
  have scaled_effect (X : CStarMatrix d d ℂ) (hX : 0 ≤ X)
      (c : ℝ) (hc : 0 < c) (hb : X ≤ c • (1 : CStarMatrix d d ℂ)) :
      0 ≤ c⁻¹ • X ∧ c⁻¹ • X ≤ 1 := by
    refine ⟨smul_nonneg (inv_nonneg.mpr hc.le) hX, ?_⟩
    have h := smul_le_smul_of_nonneg_left hb (inv_nonneg.mpr hc.le)
    simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using h
  have scale_bound (X : CStarMatrix d d ℂ) (hX : 0 ≤ X) :
      X ≤ scale X • (1 : CStarMatrix d d ℂ) := by
    have h := (IsSelfAdjoint.of_nonneg hX).le_algebraMap_norm_self
    exact h.trans (by simpa [Algebra.algebraMap_eq_smul_one] using
      smul_le_smul_of_nonneg_right (show ‖X‖ ≤ scale X by dsimp [scale]; linarith) (zero_le_one : (0 : CStarMatrix d d ℂ) ≤ 1))
  have compare (X : CStarMatrix d d ℂ) (hX : 0 ≤ X)
      (c b : ℝ) (hc : 0 < c) (hb : 0 < b)
      (hXc : X ≤ c • (1 : CStarMatrix d d ℂ))
      (hXb : X ≤ b • (1 : CStarMatrix d d ℂ)) :
      c * p (c⁻¹ • X) = b * p (b⁻¹ • X) := by
    have step (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
        (hXa : X ≤ a • (1 : CStarMatrix d d ℂ)) :
        b * p (b⁻¹ • X) = a * p (a⁻¹ • X) := by
      obtain ⟨h0,h1⟩ := scaled_effect X hX a ha hXa
      have h := effect_real_homogeneity p hpos hadd (a⁻¹ • X) h0 h1
        (a / b) (div_nonneg ha.le hb.le) ((div_le_one hb).2 hab)
      have heq : (a / b) • (a⁻¹ • X) = b⁻¹ • X := by
        rw [smul_smul]
        congr 1
        field_simp
      rw [heq] at h
      rw [h]
      field_simp
    rcases le_total c b with h | h
    · exact (step c b hc hb h hXc).symm
    · exact step b c hb hc h hXb
  let f (X : CStarMatrix d d ℂ) : ℝ := scale X * p ((scale X)⁻¹ • X)
  have at_scale (X : CStarMatrix d d ℂ) (hX : 0 ≤ X)
      (c : ℝ) (hc : 0 < c) (hb : X ≤ c • (1 : CStarMatrix d d ℂ)) :
      f X = c * p (c⁻¹ • X) := compare X hX (scale X) c
        (scale_pos X) hc (scale_bound X hX) hb
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro E h0 h1
    simpa using at_scale E h0 1 zero_lt_one (by simpa using h1)
  · intro X hX
    exact mul_nonneg (scale_pos X).le (hpos _
      (scaled_effect X hX _ (scale_pos X) (scale_bound X hX)).1
      (scaled_effect X hX _ (scale_pos X) (scale_bound X hX)).2)
  · intro X Y hX hY
    let c := scale (X+Y)
    have hc : 0 < c := scale_pos _
    have hsum := scale_bound (X+Y) (add_nonneg hX hY)
    have hXc : X ≤ c • (1 : CStarMatrix d d ℂ) :=
      (le_add_of_nonneg_right hY).trans hsum
    have hYc : Y ≤ c • (1 : CStarMatrix d d ℂ) :=
      (le_add_of_nonneg_left hX).trans hsum
    rw [at_scale (X+Y) (add_nonneg hX hY) c hc hsum,
      at_scale X hX c hc hXc, at_scale Y hY c hc hYc, smul_add,
      hadd _ _ (scaled_effect X hX c hc hXc).1 (scaled_effect Y hY c hc hYc).1
        (by rw [← smul_add]; exact (scaled_effect (X+Y) (add_nonneg hX hY) c hc hsum).2)]
    ring
  · intro X t hX ht
    by_cases hz : t = 0
    · subst t
      have hp0 := hadd 0 0 le_rfl le_rfl (by simp)
      simp only [add_zero] at hp0
      have hpz : p 0 = 0 := by linarith
      simp [f, hpz]
    have ht' : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    let c := scale X
    have hc : 0 < c := scale_pos X
    have hb := scale_bound X hX
    have htb : t • X ≤ (t*c) • (1 : CStarMatrix d d ℂ) := by
      simpa [smul_smul] using smul_le_smul_of_nonneg_left hb ht
    rw [at_scale (t • X) (smul_nonneg ht hX) (t*c) (mul_pos ht' hc) htb,
      at_scale X hX c hc hb, smul_smul]
    have hi : (t*c)⁻¹ * t = c⁻¹ := by field_simp
    rw [hi]
    ring
#print axioms effect_cone_extension
#print axioms effect_trace_unique

private theorem effect_linear_extension {d : Type*} [Fintype d] [DecidableEq d]
    (p : CStarMatrix d d ℂ → ℝ)
    (hpos : ∀ E, 0 ≤ E → E ≤ 1 → 0 ≤ p E)
    (hadd : ∀ E F, 0 ≤ E → 0 ≤ F → E + F ≤ 1 → p (E + F) = p E + p F) :
    ∃ L : CStarMatrix d d ℂ →ₗ[ℂ] ℂ,
      (∀ X, 0 ≤ X → 0 ≤ L X) ∧
      (∀ E, 0 ≤ E → E ≤ 1 → L E = (p E : ℂ)) := by
  obtain ⟨f, heffect, hfpos, hfadd, hfhom⟩ := effect_cone_extension p hpos hadd
  have hfzero : f 0 = 0 := by
    have h := hfadd 0 0 le_rfl le_rfl
    simp only [add_zero] at h
    linarith
  have diff (A B C D : CStarMatrix d d ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
      (hC : 0 ≤ C) (hD : 0 ≤ D) (h : A - B = C - D) :
      f A - f B = f C - f D := by
    have hh : A + D = C + B := sub_eq_sub_iff_add_eq_add.mp h
    have hhf := congrArg f hh
    rw [hfadd A D hA hD, hfadd C B hC hB] at hhf
    linarith
  let g : selfAdjoint (CStarMatrix d d ℂ) →ₗ[ℝ] ℝ := {
    toFun := fun X => f (X.val)⁺ - f (X.val)⁻
    map_add' := by
      intro X Y
      have h := diff ((X.val+Y.val)⁺) ((X.val+Y.val)⁻)
        ((X.val)⁺ + (Y.val)⁺) ((X.val)⁻ + (Y.val)⁻)
        (CFC.posPart_nonneg _) (CFC.negPart_nonneg _)
        (add_nonneg (CFC.posPart_nonneg _) (CFC.posPart_nonneg _))
        (add_nonneg (CFC.negPart_nonneg _) (CFC.negPart_nonneg _)) (by
          rw [CFC.posPart_sub_negPart _ (X.property.add Y.property)]
          have hX := CFC.posPart_sub_negPart X.val X.property
          have hY := CFC.posPart_sub_negPart Y.val Y.property
          calc
            X.val + Y.val = ((X.val)⁺ - (X.val)⁻) + ((Y.val)⁺ - (Y.val)⁻) := congrArg₂ (· + ·) hX.symm hY.symm
            _ = _ := by abel)
      change f (X.val+Y.val)⁺ - f (X.val+Y.val)⁻ = _
      rw [h, hfadd _ _ (CFC.posPart_nonneg _) (CFC.posPart_nonneg _),
        hfadd _ _ (CFC.negPart_nonneg _) (CFC.negPart_nonneg _)]
      ring
    map_smul' := by
      intro t X
      change f (t • X.val)⁺ - f (t • X.val)⁻ = t * (f (X.val)⁺ - f (X.val)⁻)
      rcases le_total 0 t with ht | ht
      · rw [CFC.posPart_smul_of_nonneg ht, CFC.negPart_smul_of_nonneg ht,
          hfhom _ _ (CFC.posPart_nonneg _) ht, hfhom _ _ (CFC.negPart_nonneg _) ht]
        ring
      · rw [CFC.posPart_smul_of_nonpos ht, CFC.negPart_smul_of_nonpos ht,
          hfhom _ _ (CFC.negPart_nonneg _) (neg_nonneg.mpr ht),
          hfhom _ _ (CFC.posPart_nonneg _) (neg_nonneg.mpr ht)]
        ring }
  have hg (X : CStarMatrix d d ℂ) (hX : 0 ≤ X) :
      g ⟨X, IsSelfAdjoint.of_nonneg hX⟩ = f X := by
    change f X⁺ - f X⁻ = f X
    rw [(CFC.posPart_eq_self X).2 hX,
      (CFC.negPart_eq_zero_iff X (IsSelfAdjoint.of_nonneg hX)).2 hX, hfzero, sub_zero]
  let L : CStarMatrix d d ℂ →ₗ[ℂ] ℂ := {
    toFun := fun X => (g (realPart X) : ℂ) + Complex.I * (g (imaginaryPart X) : ℂ)
    map_add' := by
      intro X Y
      simp only [map_add, Complex.ofReal_add]
      ring
    map_smul' := by
      intro z X
      simp only [realPart_smul, imaginaryPart_smul, map_sub, map_add,
        map_smul, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
        RingHom.id_apply]
      conv_rhs => rw [← Complex.re_add_im z]
      ring_nf
      simp [Complex.I_sq]
      ring }
  have hL (X : CStarMatrix d d ℂ) (hX : 0 ≤ X) : L X = (f X : ℂ) := by
    have hreal : realPart X = ⟨X, IsSelfAdjoint.of_nonneg hX⟩ :=
      Subtype.ext (IsSelfAdjoint.of_nonneg hX).coe_realPart
    change (g (realPart X) : ℂ) + Complex.I * (g (imaginaryPart X) : ℂ) = _
    rw [hreal, (IsSelfAdjoint.of_nonneg hX).imaginaryPart, map_zero, hg X hX]
    simp
  exact ⟨L, fun X hX => by rw [hL X hX]; exact_mod_cast hfpos X hX,
    fun E h0 h1 => by rw [hL E h0, heffect E h0 h1]⟩

/-- Every normalized finitely additive probability on all effects has one density representative. -/
theorem effect_density_representation {d : Type*} [Fintype d] [DecidableEq d]
    (p : CStarMatrix d d ℂ → ℝ)
    (hpos : ∀ E, 0 ≤ E → E ≤ 1 → 0 ≤ p E)
    (hadd : ∀ E F, 0 ≤ E → 0 ≤ F → E + F ≤ 1 → p (E + F) = p E + p F)
    (hnorm : p 1 = 1) :
    ∃! ρ : Matrix d d ℂ, ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧
      ∀ E : CStarMatrix d d ℂ, 0 ≤ E → E ≤ 1 →
        Matrix.trace (ρ * CStarMatrix.ofMatrix.symm E) = (p E : ℂ) := by
  obtain ⟨L, hLpos, hLeffect⟩ := effect_linear_extension p hpos hadd
  let M : PhyslibLeaf.MatrixMap d (Fin 1) ℂ := {
    toFun := fun X => L (CStarMatrix.ofMatrix X) • 1
    map_add' := by intro X Y; change L (CStarMatrix.ofMatrix X + CStarMatrix.ofMatrix Y) • _ = _; rw [map_add, add_smul]
    map_smul' := by intro c X; change L (c • CStarMatrix.ofMatrix X) • _ = _; rw [map_smul, smul_smul]; rfl }
  have hM : M.IsPositive := by
    intro X hX
    change (L (CStarMatrix.ofMatrix X) • (1 : Matrix (Fin 1) (Fin 1) ℂ)).PosSemidef
    apply Matrix.PosSemidef.smul (Matrix.PosSemidef.one)
    exact hLpos _ (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hX.nonneg)
  let ρ : Matrix d d ℂ := M.dual 1
  have hρ : ρ.PosSemidef := hM.dual Matrix.PosSemidef.one
  have rep (X : Matrix d d ℂ) : Matrix.trace (ρ * X) = L (CStarMatrix.ofMatrix X) := by
    rw [Matrix.trace_mul_comm, ← PhyslibLeaf.MatrixMap.Dual.trace_eq]
    change Matrix.trace ((L (CStarMatrix.ofMatrix X) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) * 1) = _
    simp [Matrix.trace_smul, Matrix.trace_one]
  refine ⟨ρ, ⟨hρ, ?_, ?_⟩, ?_⟩
  · have h := rep 1
    change Matrix.trace (ρ * 1) = L 1 at h
    simpa [hLeffect 1 zero_le_one le_rfl, hnorm] using h
  · intro E h0 h1
    exact (rep (CStarMatrix.ofMatrix.symm E)).trans (hLeffect E h0 h1)
  · intro σ hσ
    apply effect_trace_unique σ ρ
    intro E h0 h1
    exact (hσ.2.2 E h0 h1).trans ((rep (CStarMatrix.ofMatrix.symm E)).trans
      (hLeffect E h0 h1)).symm
#print axioms effect_linear_extension
#print axioms effect_density_representation
end D5.S3.Quantum.Foundation.EffectProbabilityExtension
