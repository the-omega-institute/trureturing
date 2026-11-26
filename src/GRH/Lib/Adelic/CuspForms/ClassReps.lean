import GRH.Lib.GLn.SchurModule.WeightRepBasic
import GRH.Lib.Adelic.Landherr.WeakApprox
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular forms
(known result; see Lib.Adelic.CuspForms.Petersson).

This file: p-adic gauge on algebraic forms: invariance, ultrametric, integral module, weak
approximation. Norm bounded by dual functionals; triangle inequality for finite sums. Class sets,
p-integral representatives, integrality of forms supported on one class. -/

open NormedField Space IsUltrametricDist Matrix Function PolyRep
variable {E n} [Field E] [CMType E] [Fintype n] {κ e p} [Fact p.Prime] (g d : Gf E n)
  (σ : E →+* ℂ_[p]) {k}

lemma adeleExtension_mem_intGL (hk : k ∈ integralAbove n p) : .map (adeleExtension σ) k.1 ∈ intGL n
  valuation.integer := mem_intGL.2 (by convert mem_intGL.1 (hk (placeOfEmb σ) (by simp)) <;>
  exact (exists_placeOfEmb_extension σ).choose_spec.2.2.2.le_one_iff_le_one)

variable (p) in /-- Weak approximation above `p`. -/

lemma exists_mul_mem_integralAbove (V := stdSpace E n) : ∃ γ, V.embFin γ * g ∈ integralAbove n p ∧
  d * (V.embFin γ * g) *
  d⁻¹ ∈ integralAbove n p := ((V.weak_approximation (finite_natCast_mem p)).exists_mem_open
  ((isOpen_Kf.inter (isOpen_Kf.preimage_of_continuous (f := (d * · * d⁻¹)))).preimage_of_continuous
  (f := (·.2 * g))) ⟨g⁻¹, by simp⟩).rec (by simp [localLevel, mem_Kf_iff, embFin, Γ]; grind)

variable [ι : PadicPlace p] {ξ} (c γ) (φ : AlgForm (E := E) n κ e) {α s C} {f : α → _}

lemma weylGauge_embFin : weylGauge κ e ((stdSpace ..).embFin γ * g) (weightRep κ e _ γ ξ) =
  weylGauge κ e g ξ := by
  simp [weylGauge, map_weightRep, ← map_mul]; congr!; aesop (add simp [mul_assoc, inv_mul_eq_one])

/-- The gauge of ξ at g is unchanged when g is multiplied on the right by an element k integral
above p. -/
lemma weylGauge_mul (hk : k ∈ integralAbove n p) : weylGauge κ e (g * k) ξ = weylGauge κ e g ξ :=
  have {k} a g : weylGauge κ e (g * k⁻¹) ξ ≤ weylGauge .. := by simpa [weylGauge, ← Pi.mul_def]
                  using
    (norm_mulVec_le (weylRep_entry_mem _ fun _ ↦ adeleExtension_mem_intGL (k := k) _ a) (_ *ᵥ _))
  by grind [inv_mem, mul_inv_cancel_right]

lemma weylGauge_smul : weylGauge κ e g (c • ξ) = ‖ιₚ c‖ * weylGauge κ e g ξ := by
  simp [weylGauge, ← norm_smul, ← mulVec_smul, comp_def]; rfl

lemma weylGauge_le_one_iff ξ (hk : k ∈ integralAbove n p) : weylGauge κ e k ξ ≤ 1 ↔
  ∀ i, ‖ιₚ (ξ i)‖ ≤ 1 := by
  rw [← one_mul k, weylGauge_mul _ hk]; simp [weylGauge, weylRep, pi_norm_le_iff_of_nonneg]

lemma weylGauge_sum_le : 0 ≤ C → (∀ a ∈ s, weylGauge κ e g (f a) ≤ C) →
  weylGauge κ e g (∑ a ∈ s, f a) ≤ C := by
  simp_all [weylGauge, comp_def, ← s.sum_fn, mulVec_sum, norm_sum_le_of_forall_le_of_nonneg]

/-- The bound c for the form φ read at d: the gauge of φ(g) at gd and ι is at most c for every
g. -/
def GaugeLe := ∀ g, weylGauge κ e (g * d) (φ.1 g) ≤ c

/-- The valuation ring O_ι ⊂ ℂ of complex numbers whose image under ι : ℂ → ℂ_p has absolute
value at most 1. -/
noncomputable abbrev embValRing := (valuation.comap ιₚ).valuationSubring

/-- The O_ι-module of forms φ in S that are integral at d: the value φ(g) has gauge at most 1 at
gd for every g. -/
noncomputable def integralFormsAt (S : Submodule ℂ (AlgForm n κ e)) d := S.restrictScalars
  embValRing ⊓ by use! .ofPred (GaugeLe d 1), ?_, ?_, fun a ↦ (weylGauge_smul .. |>.trans_le <|
  mul_le_one₀ a.2 ?_ <| · ·) <;> simp_all [GaugeLe, weylGauge, (norm_add_le_max ..).trans]

lemma Kf_le_localLevel {S} : Kf E n ≤ localLevel n S := fun _ h w _ ↦ mem_Kf_iff.1 h w

lemma weylGauge_le_one_of_integralAbove (h : ∀ g ∈ integralAbove n p, ∀ i, ‖ιₚ (φ.1 g i)‖ ≤ 1) g :
  weylGauge κ e g (φ.1 g) ≤ 1 :=
  by cases exists_mul_mem_integralAbove p g 1; rw [← weylGauge_embFin, ← φ.2.2,
  weylGauge_le_one_iff] <;> tauto

variable {T} {n : _} [Fintype T] [Fintype n] {κ : T → _} (σ : ℂ ≃+* ℂ)

/-- Duality for the Gram norm, σ an automorphism of ℂ: if |σ(c·v)| ≤ C for every c with |σ(c·w)|
≤ ‖σ(w)‖ for all w, then ‖σ(v)‖ ≤ C. -/
lemma sqrt_weylNormSq_le_of_dual {v : WeylIndex n κ → _} {C} (h : ∀ c,
  (∀ w, ‖σ (c ⬝ᵥ w)‖ ≤ √(weylNormSq (σ ∘ w))) → ‖σ (c ⬝ᵥ v)‖ ≤ C) : √(weylNormSq (σ ∘ v)) ≤ C := by
  cases σ.surjective.comp_left ((√(weylNormSq (σ ∘ v)))⁻¹ • star (σ ∘ v) ᵥ* weylGramOver)
  rcases (Real.abs_le_sqrt <| posDef_cauchy_schwarz weylGram_posDef (σ ∘ v) ·),
    σ.toRingHom.map_dotProduct ‹_›, h ‹_›
  simp_all [← dotProduct_mulVec, ← coe_weylNormSq, abs_of_nonneg, inv_mul_eq_div, div_le_of_le_mul₀]

lemma sqrt_weylNormSq_sum_le {α} s (f : α → WeylIndex n κ → ℂ) : √(weylNormSq (σ ∘ ∑ a ∈ s, f a)) ≤
    ∑ a ∈ s, √(weylNormSq (σ ∘ f a)) :=
  sqrt_weylNormSq_le_of_dual σ (by simp_all [dotProduct_sum, norm_sum_le_of_le])

variable {E n : Type} [Field E] [CMType E] [Fintype n]
  {K : Subgroup (Gf E n)}

/-- The set of classes of I_n at level K: double cosets of the finite adelic unitary group by
its rational points on the left and K on the right. -/
abbrev StdClasses (K : Subgroup (Gf E n)) := DoubleCosets (stdSpace ..).Γf K

lemma exists_reps_integralAbove (p : ℕ) [Fact p.Prime] : ∃ r : StdClasses K → _,
    (∀ c, DoubleCoset.mk _ _
  (r c) = c) ∧ ∀ c, r c ∈ integralAbove n p := ⟨_, (·.eq_mk_iff_out.2 (DoubleCoset.rel_iff.2
  ⟨_, ⟨_, rfl⟩, 1, by aesop⟩) |>.symm), (exists_mul_mem_integralAbove p ·.out 1 |>.choose_spec.1)⟩

variable [HasFiniteType stdRatPoints K] {κ e : _} {χ : K →* ℂ} [Fact (χ =ᶠ[nhds 1] 1)]

noncomputable instance : Fintype (StdClasses K) := @.ofFinite _ HasFiniteType.finite_classes

/-- For K inside the stabiliser of the standard lattice and χ with values of finite order, the
delta form attached to χ, x, v has, at every point g, gauge at ι at most the gauge of v at
x. -/
lemma weylGauge_deltaForm_le [hK : IsLevel K] (hχ : ∀ k,
  IsOfFinOrder (χ k)) {p} [Fact p.Prime] [PadicPlace p] {x v g} : weylGauge κ e g
  ((deltaForm stdEmbFin (Space.weightRep κ e _) χ x v).1.1 g) ≤ weylGauge κ e x v := by
  simp [deltaForm]; apply weylGauge_sum_le <;> intros; swap; split
  simp [weylGauge_smul, ← weylGauge_embFin x ‹_›⁻¹,
    ← weylGauge_mul (_ * x) (Kf_le_localLevel (hK.1 ‹_›)), mul_assoc]
  erw [(ιₚ.isOfFinOrder (hχ _)).norm_eq_one]
  repeat simp [weylGauge]

/-- For a level K with a character χ whose values have finite order and σ ∈ Aut ℂ, the value at
any g of the delta form δ_x(v) on U(I_n) satisfies ‖σ δ_x(v)(g)‖² ≤ |Aut(x)|²·‖σ v‖² in the
Gram norm. -/
lemma weylNormSq_deltaForm_le (hχ : ∀ k, IsOfFinOrder (χ k)) (σ : ℂ ≃+* ℂ) x v g :
  weylNormSq (σ ∘ (deltaForm stdEmbFin (Space.weightRep κ e _) χ x v).1.1 g) ≤
  Nat.card (classAut stdEmbFin.range K x) ^ 2 * weylNormSq (σ ∘ v) := by
  rw [← Real.sqrt_le_sqrt_iff (by bound)]; simp [deltaForm]
  grw [sqrt_weylNormSq_sum_le, Finset.sum_le_card_nsmul]; simp; gcongr
  grind
  intros; split; erw [weylNormSq_comp_smul, weylNormSq, ← gramForm_apply, gramForm_map_weightRep σ,
    (σ.toMonoidHom.isOfFinOrder (hχ _)).norm_eq_one]; repeat simp [weylNormSq, gramForm_apply]
