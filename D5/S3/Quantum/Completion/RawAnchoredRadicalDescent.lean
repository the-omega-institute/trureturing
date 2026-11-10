/- GID: D5/S3/Quantum/Completion/RawAnchoredRadicalDescent
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/RawAnchoredRadicalDescent
   mirror-E: none(waiver:unbounded-original-domain-descent)
   anchors: []
   utility: none
   digest: Original directed histories yield fibre collapse and the complete Hilbert classification. -/

import D5.S3.Quantum.Completion.RawAnchoredFourierQuotient

/-! All ordered histories on the original unital magma determine the zero-comparison
quotient, its Eisenstein module and the unique minimal Hilbert representation. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Completion.RawAnchoredRadicalDescent

universe u v w

open D5.S3.QuadraticForms.ThreeWayPositiveKernel

/-- The actual zero fibre in the constructed quotient. -/
def N {M : Type*} [MulOneClass M] (c : M → M → ℝ) : Set M :=
  {a | gamma c a = 0}

/-- The actual ordered relation of equal gamma labels. -/
def K {M : Type*} [MulOneClass M] (c : M → M → ℝ) : Set (M × M) :=
  {p | gamma c p.1 = gamma c p.2}

private theorem comparison_bound {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b u v : M) :
    c (a * u) (b * v) ≤ 3 * (c a b + c u v) := by
  have hb := h.balance a b u v
  linarith [h.nonneg (a * U u) (b * U v), h.nonneg (a * U (U u)) (b * U (U v))]

private theorem directed_fibre_differences {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b z : M)
    (hab : (a, b) ∈ K c) :
    c a (b * z) - c b (b * z) =
        -2 * quotientForm c (beta c a - beta c b) (beta c z) ∧
      c (b * z) a - c (b * z) b =
        -2 * quotientForm c (beta c z) (beta c a - beta c b) := by
  have hw : beta c a - beta c b ∈ W c := (Submodule.Quotient.eq _).1 hab
  have hc := gamma_fibre_zero_comparison U c h a b hab
  have he : beta c (b * z) = beta c b + beta c z + defect c b z := by
    unfold defect
    abel
  constructor
  · have ht := W_isotropic U c h _ _ hw (defect_mem_W c b z)
    have hb : quotientForm c (beta c a - beta c b) (beta c (b * z)) =
        quotientForm c (beta c a - beta c b) (beta c b) +
        quotientForm c (beta c a - beta c b) (beta c z) := by
      rw [he, map_add, map_add, ht, add_zero]
    simp only [map_sub, LinearMap.sub_apply, quotientForm_beta c (h.diagonal 1),
      kernel, hc.1, h.diagonal] at hb
    simp only [map_sub, LinearMap.sub_apply, quotientForm_beta c (h.diagonal 1), kernel]
    linarith
  · have ht := W_isotropic U c h _ _ (defect_mem_W c b z) hw
    have hb : quotientForm c (beta c (b * z)) (beta c a - beta c b) =
        quotientForm c (beta c b) (beta c a - beta c b) +
        quotientForm c (beta c z) (beta c a - beta c b) := by
      rw [he, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ht, add_zero]
    simp only [map_sub, quotientForm_beta c (h.diagonal 1), kernel, hc.2, h.diagonal] at hb
    simp only [map_sub, quotientForm_beta c (h.diagonal 1), kernel]
    linarith

private theorem directed_fibre_bounds {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b z : M)
    (hab : (a, b) ∈ K c) :
    |quotientForm c (beta c a - beta c b) (beta c z)| ≤ (3 / 2 : ℝ) * r c z ∧
      |quotientForm c (beta c z) (beta c a - beta c b)| ≤ (3 / 2 : ℝ) * q c z := by
  have hc := gamma_fibre_zero_comparison U c h a b hab
  have hd := directed_fibre_differences U c h a b z hab
  have h₁ := comparison_bound U c h a b 1 z
  have h₂ := comparison_bound U c h b b 1 z
  have h₃ := comparison_bound U c h b a z 1
  have h₄ := comparison_bound U c h b b z 1
  simp only [mul_one, hc.1, hc.2, h.diagonal, zero_add] at h₁ h₂ h₃ h₄
  dsimp [q, r]
  constructor <;> rw [abs_le] <;>
    constructor <;> linarith [hd.1, hd.2, h.nonneg a (b * z), h.nonneg b (b * z),
      h.nonneg (b * z) a, h.nonneg (b * z) b]

private theorem N_one {M : Type*} [MulOneClass M] (c : M → M → ℝ) : (1 : M) ∈ N c :=
  gamma_one c

private theorem N_marker {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) {a : M} (ha : a ∈ N c) :
    U a ∈ N c := by
  change gamma c (U a) = 0
  rw [gamma_marker U c h, ha, map_zero]

private theorem N_children {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) {u x : M}
    (hu : u ∈ N c) (hx : x ∈ N c) (k : ℕ) : x * U^[k] u ∈ N c := by
  change gamma c (x * U^[k] u) = 0
  rw [gamma_phase_product U c h, hx, hu, zero_add]
  induction k with
  | zero => rfl
  | succ k ih => simpa only [Function.iterate_succ_apply', ih, map_zero]

/-- The algebraic complex structure before any positivity claim. -/
def J {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) : V c →ₗ[ℝ] V c :=
  (Real.sqrt 3)⁻¹ • ((2 : ℝ) • markerQuotient U c h + LinearMap.id)

private theorem J_square {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x : V c) :
    J U c h (J U c h x) = -x := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have he : J U c h (J U c h x) + x =
      (4 / 3 : ℝ) • (x + markerQuotient U c h x +
        markerQuotient U c h (markerQuotient U c h x)) := by
    simp only [J, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
      map_add, map_smul]
    match_scalars <;> field_simp <;> nlinarith
  rw [marker_cyclotomic U c h, smul_zero] at he
  exact eq_neg_iff_add_eq_zero.mpr he

private theorem phase_cube : omega ^ 3 = 1 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs₃ := congrArg (fun t : ℝ => t * Real.sqrt 3) hs
  apply Complex.ext <;> norm_num [omega, pow_succ, Complex.mul_re, Complex.mul_im]
  all_goals nlinarith

private def phaseCharacter : AddChar (ZMod 3) ℂ := AddChar.zmodChar 3 phase_cube

private theorem phase_cases (k : ZMod 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  have hk := k.val_lt
  have hc := (ZMod.natCast_zmod_val k).symm
  have hv : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
  rcases hv with hv | hv | hv
  · left; simpa [hv] using hc
  · right; left; simpa [hv] using hc
  · right; right; simpa [hv] using hc

private theorem phaseCharacter_injective : Function.Injective phaseCharacter := by
  intro a b hab
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  rcases phase_cases a with rfl | rfl | rfl
  all_goals rcases phase_cases b with rfl | rfl | rfl
  all_goals try rfl
  all_goals norm_num [phaseCharacter, AddChar.zmodChar_apply, ZMod.val_one, ZMod.val_ofNat,
      omega, pow_succ,
      Complex.ext_iff, Complex.mul_re, Complex.mul_im] at hab
  all_goals nlinarith

private def complexMode {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (α : V c →ₗ[ℝ] ℝ) :
    V c →ₗ[ℝ] ℂ :=
  (Complex.ofRealLI.toLinearMap.comp α) -
    Complex.I • (Complex.ofRealLI.toLinearMap.comp (α.comp (J U c h)))

private theorem complexMode_re {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (α : V c →ₗ[ℝ] ℝ) (x : V c) :
    (complexMode U c h α x).re = α x := by
  simp [complexMode, Complex.mul_re]

private theorem complexMode_marker {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (α : V c →ₗ[ℝ] ℝ) (x : V c) :
    complexMode U c h α (markerQuotient U c h x) = omega * complexMode U c h α x := by
  have hn : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hj : complexMode U c h α (J U c h x) =
      Complex.I * complexMode U c h α x := by
    apply Complex.ext <;> simp [complexMode, J_square U c h, Complex.mul_re, Complex.mul_im]
  have hr : markerQuotient U c h x =
      (Real.sqrt 3 / 2) • J U c h x - (1 / 2 : ℝ) • x := by
    simp only [J, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
    match_scalars <;> field_simp <;> ring
  rw [hr, map_sub, map_smul, map_smul, hj]
  apply Complex.ext <;> simp [omega, Complex.mul_re, Complex.mul_im] <;> ring

private theorem complexMode_bound {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (α : V c →ₗ[ℝ] ℝ)
    (L : ℝ) (hL : 0 ≤ L) (ha : ∀ n ∈ N c, |α (beta c n)| ≤ L)
    (n : M) (hn : n ∈ N c) :
    Complex.normSq (complexMode U c h α (beta c n)) ≤ 10 * L ^ 2 := by
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs₁ : 1 ≤ Real.sqrt (3 : ℝ) := (Real.one_le_sqrt).2 (by norm_num)
  have h₀ := ha n hn
  have h₁ := ha (U n) (N_marker U c h hn)
  have hj : α (J U c h (beta c n)) =
      (Real.sqrt 3)⁻¹ * (2 * α (beta c (U n)) + α (beta c n)) := by
    simp [J, map_add, map_smul, markerQuotient_beta, smul_eq_mul]
    ring
  have hsum : |2 * α (beta c (U n)) + α (beta c n)| ≤ 3 * L := by
    rw [abs_le] at h₀ h₁ ⊢
    constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2]
  have hjabs : |α (J U c h (beta c n))| ≤ 3 * L := by
    rw [hj, abs_mul, abs_inv, abs_of_pos hs]
    calc
      _ = |2 * α (beta c (U n)) + α (beta c n)| / Real.sqrt 3 := by ring
      _ ≤ (3 * L) / Real.sqrt 3 := div_le_div_of_nonneg_right hsum (le_of_lt hs)
      _ ≤ 3 * L := by
        apply (div_le_iff₀ hs).2
        nlinarith [mul_nonneg hL (sub_nonneg.mpr hs₁)]
  have hsq₀ : α (beta c n) ^ 2 ≤ L ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hL).2 h₀
  have hsq₁ : α (J U c h (beta c n)) ^ 2 ≤ (3 * L) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 3 * L)).2 hjabs
  simp [Complex.normSq_apply, complexMode, Complex.mul_re, Complex.mul_im]
  nlinarith

private theorem actual_mode_recursion {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (α : V c →ₗ[ℝ] ℝ)
    (a u : M) (k : ZMod 3) :
    complexMode U c h α (beta c (a * U^[k.val] u)) =
      complexMode U c h α (beta c a) +
      phaseCharacter k * complexMode U c h α (beta c u) +
      phaseCharacter⁻¹ k * complexMode U c h α (defect c a u) := by
  have hp := (raw_anchored_radical_descent U c h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a u
  have h₀ : beta c (a * u) = beta c a + beta c u + defect c a u := by
    unfold defect
    abel
  rcases phase_cases k with rfl | rfl | rfl
  all_goals norm_num [phaseCharacter, AddChar.zmodChar_apply, AddChar.inv_apply,
    ZMod.val_one, ZMod.val_ofNat, show -(2 : ZMod 3) = 1 by decide,
    Function.iterate_succ_apply']
  · rw [h₀, map_add, map_add]
  · rw [hp.1, map_add, map_add]
    simp only [complexMode_marker]
    ring
  · rw [hp.2, map_add, map_add]
    simp only [complexMode_marker, show (-2 : ZMod 3).val = 1 by decide, pow_one]
    ring

/-- Every actual zero-fibre label has zero beta, using both directed history bounds. -/
theorem raw_zero_fibre_vanishes {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    ∀ u ∈ N c, beta c u = 0 := by
  intro u hu
  apply quotient_joint_nondegenerate c (h.diagonal 1)
  · intro z
    let α : V c →ₗ[ℝ] ℝ := (quotientForm c).flip (beta c z)
    let L : ℝ := (3 / 2 : ℝ) * r c z
    have hL : 0 ≤ L := mul_nonneg (by norm_num) (h.nonneg 1 z)
    have ha (n : M) (hn : n ∈ N c) : |α (beta c n)| ≤ L := by
      have hk : (n, 1) ∈ K c := by change gamma c n = gamma c 1; rw [hn, gamma_one]
      simpa [α, beta_one] using (directed_fibre_bounds U c h n 1 z hk).1
    have hv := D5.S3.Quantum.Completion.ThreePhaseHistoryRigidity.bounded_phase_recursion_vanishes
      U u (N c) (N_one c) (fun x hx k => N_children U c h hu hx k.val)
      phaseCharacter phaseCharacter_injective
      (fun x => complexMode U c h α (beta c x))
      (fun x => complexMode U c h α (defect c x u)) (10 * L ^ 2)
      (fun x hx => complexMode_bound U c h α L hL ha x hx)
      (fun x _ k => actual_mode_recursion U c h α x u k)
    have hre := congrArg Complex.re hv
    simpa [complexMode_re, α] using hre
  · intro z
    let α : V c →ₗ[ℝ] ℝ := quotientForm c (beta c z)
    let L : ℝ := (3 / 2 : ℝ) * q c z
    have hL : 0 ≤ L := mul_nonneg (by norm_num) (h.nonneg z 1)
    have ha (n : M) (hn : n ∈ N c) : |α (beta c n)| ≤ L := by
      have hk : (n, 1) ∈ K c := by change gamma c n = gamma c 1; rw [hn, gamma_one]
      simpa [α, beta_one] using (directed_fibre_bounds U c h n 1 z hk).2
    have hv := D5.S3.Quantum.Completion.ThreePhaseHistoryRigidity.bounded_phase_recursion_vanishes
      U u (N c) (N_one c) (fun x hx k => N_children U c h hu hx k.val)
      phaseCharacter phaseCharacter_injective
      (fun x => complexMode U c h α (beta c x))
      (fun x => complexMode U c h α (defect c x u)) (10 * L ^ 2)
      (fun x hx => complexMode_bound U c h α L hL ha x hx)
      (fun x _ k => actual_mode_recursion U c h α x u k)
    have hre := congrArg Complex.re hv
    simpa [complexMode_re, α] using hre

private theorem gamma_inverse_label {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a : M) :
    gamma c (U a * U (U a)) = -gamma c a := by
  have hc := congrArg (W c).mkQ (marker_cyclotomic U c h (beta c a))
  simp only [map_add, map_zero, markerQuotient_beta] at hc
  change gamma c a + gamma c (U a) + gamma c (U (U a)) = 0 at hc
  rw [gamma_mul]
  apply eq_neg_iff_add_eq_zero.mpr
  convert hc using 1 <;> abel

private theorem fibre_linear_vanishes {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    (α : V c →ₗ[ℝ] ℝ) (L : ℝ)
    (hb : ∀ a b, (a, b) ∈ K c → |α (beta c a - beta c b)| ≤ L) :
    ∀ a b, (a, b) ∈ K c → α (beta c a - beta c b) = 0 := by
  let S : Set ℝ := Set.range (fun p : {p : M × M // p ∈ K c} =>
    |α (beta c p.val.1 - beta c p.val.2)|)
  have hne : S.Nonempty := ⟨0, ⟨⟨(1, 1), rfl⟩, by simp⟩⟩
  have hbd : BddAbove S := by
    refine ⟨L, ?_⟩
    rintro t ⟨p, rfl⟩
    exact hb _ _ p.property
  have hup (a b : M) (hab : (a, b) ∈ K c) :
      |α (beta c a - beta c b)| ≤ sSup S :=
    le_csSup hbd ⟨⟨(a, b), hab⟩, rfl⟩
  have hcontract (a b : M) (hab : (a, b) ∈ K c) :
      |α (beta c a - beta c b)| ≤ (2 / 3 : ℝ) * sSup S := by
    let d := U a * U (U a)
    have haN : a * d ∈ N c := by
      change gamma c (a * d) = 0
      rw [gamma_mul, gamma_inverse_label U c h]
      exact add_neg_cancel _
    have hbN : b * d ∈ N c := by
      change gamma c (b * d) = 0
      rw [gamma_mul, gamma_inverse_label U c h]
      change gamma c a = gamma c b at hab
      rw [hab, add_neg_cancel]
    have hz : α (beta c (a * d) - beta c (b * d)) = 0 := by
      rw [raw_zero_fibre_vanishes U c h _ haN, raw_zero_fibre_vanishes U c h _ hbN]
      simp
    have hk (t : M) : (a * t, b * t) ∈ K c := by
      change gamma c (a * t) = gamma c (b * t)
      rw [gamma_mul, gamma_mul, show gamma c a = gamma c b from hab]
    have he₁ := congrArg α (unweighted_sum U c h a d)
    have he₂ := congrArg α (unweighted_sum U c h b d)
    simp only [map_add, map_smul, smul_eq_mul] at he₁ he₂
    have he : 3 * α (beta c a - beta c b) =
        α (beta c (a * U d) - beta c (b * U d)) +
        α (beta c (a * U (U d)) - beta c (b * U (U d))) := by
      simp only [map_sub] at hz ⊢
      linarith
    have ht : |3 * α (beta c a - beta c b)| ≤ sSup S + sSup S := by
      rw [he]
      exact (abs_add_le _ _).trans
        (add_le_add (hup _ _ (hk (U d))) (hup _ _ (hk (U (U d)))))
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at ht
    linarith
  have hs : sSup S ≤ (2 / 3 : ℝ) * sSup S := by
    apply csSup_le hne
    rintro t ⟨p, rfl⟩
    exact hcontract _ _ p.property
  have hs0 : sSup S ≤ 0 := by linarith
  intro a b hab
  exact abs_eq_zero.mp (le_antisymm ((hup a b hab).trans hs0) (abs_nonneg _))

/-- The same original gamma fibre has a unique anchored comparison vector. -/
theorem raw_gamma_fibre_collapse {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b : M)
    (hab : gamma c a = gamma c b) : beta c a = beta c b := by
  apply sub_eq_zero.mp
  apply quotient_joint_nondegenerate c (h.diagonal 1)
  · intro z
    exact fibre_linear_vanishes U c h ((quotientForm c).flip (beta c z))
      ((3 / 2 : ℝ) * r c z) (fun x y hxy => (directed_fibre_bounds U c h x y z hxy).1)
      a b hab
  · intro z
    exact fibre_linear_vanishes U c h (quotientForm c (beta c z))
      ((3 / 2 : ℝ) * q c z) (fun x y hxy => (directed_fibre_bounds U c h x y z hxy).2)
      a b hab

/-- Both one-point and both ordered comparison readouts are constant on actual gamma fibres. -/
theorem raw_directed_comparison_descent {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b : M)
    (hab : gamma c a = gamma c b) :
    q c a = q c b ∧ r c a = r c b ∧
      (∀ z, c a z = c b z) ∧ (∀ z, c z a = c z b) := by
  have hv := raw_gamma_fibre_collapse U c h a b hab
  have hc := gamma_fibre_zero_comparison U c h a b hab
  have h₁ := congrArg (fun x => quotientForm c x (beta c b)) hv
  have h₂ := congrArg (quotientForm c (beta c a)) hv
  simp only [quotientForm_beta c (h.diagonal 1), kernel, h.diagonal, hc.1] at h₁ h₂
  have hq : q c a = q c b := by linarith
  have hr : r c a = r c b := by linarith
  refine ⟨hq, hr, ?_, ?_⟩
  · intro z
    have hz := congrArg (fun x => quotientForm c x (beta c z)) hv
    simp only [quotientForm_beta c (h.diagonal 1), kernel] at hz
    linarith
  · intro z
    have hz := congrArg (quotientForm c (beta c z)) hv
    simp only [quotientForm_beta c (h.diagonal 1), kernel] at hz
    linarith

/-- The actual gamma image, closed under addition and the original inverse label. -/
def visibleGroup {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) : AddSubgroup (GammaSpace c) where
  carrier := Set.range (gamma c)
  zero_mem' := ⟨1, gamma_one c⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, gamma_mul c a b⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨U a * U (U a), gamma_inverse_label U c h a⟩

def visibleLabel {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a : M) : visibleGroup U c h :=
  ⟨gamma c a, ⟨a, rfl⟩⟩

private theorem visibleLabel_surjective {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    Function.Surjective (visibleLabel U c h) := by
  rintro ⟨x, a, rfl⟩
  exact ⟨a, rfl⟩

private theorem visibleLabel_mul {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b : M) :
    visibleLabel U c h (a * b) = visibleLabel U c h a + visibleLabel U c h b :=
  Subtype.ext (gamma_mul c a b)

def visibleMarker {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    visibleGroup U c h →+ visibleGroup U c h where
  toFun x := ⟨rho U c h x.val, by
    obtain ⟨a, ha⟩ := x.property
    exact ⟨U a, (gamma_marker U c h a).trans (congrArg (rho U c h) ha)⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

private theorem visibleLabel_marker {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a : M) :
    visibleLabel U c h (U a) = visibleMarker U c h (visibleLabel U c h a) :=
  Subtype.ext (gamma_marker U c h a)

private def originalLabel {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x : visibleGroup U c h) : M :=
  Classical.choose x.property

private theorem originalLabel_spec {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x : visibleGroup U c h) :
    gamma c (originalLabel U c h x) = x.val := Classical.choose_spec x.property

/-- The full directed comparison on the actual additive image. -/
def visibleComparison {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    (x y : visibleGroup U c h) : ℝ := c (originalLabel U c h x) (originalLabel U c h y)

private theorem visibleComparison_label {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b : M) :
    visibleComparison U c h (visibleLabel U c h a) (visibleLabel U c h b) = c a b := by
  have ha := raw_directed_comparison_descent U c h _ a
    (originalLabel_spec U c h (visibleLabel U c h a))
  have hb := raw_directed_comparison_descent U c h _ b
    (originalLabel_spec U c h (visibleLabel U c h b))
  exact (ha.2.2.1 _).trans (hb.2.2.2 _)

private theorem visibleComparison_nonneg {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x y : visibleGroup U c h) :
    0 ≤ visibleComparison U c h x y := h.nonneg _ _

private theorem visibleComparison_diagonal {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x : visibleGroup U c h) :
    visibleComparison U c h x x = 0 := h.diagonal _

private theorem visibleComparison_balance {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x y u v : visibleGroup U c h) :
    visibleComparison U c h (x + u) (y + v) +
      visibleComparison U c h (x + visibleMarker U c h u) (y + visibleMarker U c h v) +
      visibleComparison U c h (x + visibleMarker U c h (visibleMarker U c h u))
        (y + visibleMarker U c h (visibleMarker U c h v)) =
      3 * visibleComparison U c h x y + 3 * visibleComparison U c h u v := by
  obtain ⟨a, rfl⟩ := visibleLabel_surjective U c h x
  obtain ⟨b, rfl⟩ := visibleLabel_surjective U c h y
  obtain ⟨d, rfl⟩ := visibleLabel_surjective U c h u
  obtain ⟨e, rfl⟩ := visibleLabel_surjective U c h v
  have hb :
      visibleComparison U c h (visibleLabel U c h (a * d)) (visibleLabel U c h (b * e)) +
      visibleComparison U c h (visibleLabel U c h (a * U d)) (visibleLabel U c h (b * U e)) +
      visibleComparison U c h (visibleLabel U c h (a * U (U d)))
        (visibleLabel U c h (b * U (U e))) =
      3 * visibleComparison U c h (visibleLabel U c h a) (visibleLabel U c h b) +
      3 * visibleComparison U c h (visibleLabel U c h d) (visibleLabel U c h e) := by
    simpa only [visibleComparison_label] using h.balance a b d e
  simpa only [visibleLabel_mul, visibleLabel_marker] using hb

/-- The original directed comparison on the constructed image is translation invariant. -/
theorem raw_visible_translation_invariant {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    (x y z : visibleGroup U c h) :
    visibleComparison U c h (x + z) (y + z) = visibleComparison U c h x y := by
  let f : visibleGroup U c h → ℝ := fun t => visibleComparison U c h (x + t) (y + t)
  let S : Set ℝ := Set.range f
  have hne : S.Nonempty := ⟨f 0, ⟨0, rfl⟩⟩
  have hbd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact visibleComparison_nonneg U c h _ _
  have hm (t : visibleGroup U c h) : sInf S ≤ f t := csInf_le hbd ⟨t, rfl⟩
  have hstep (t w : visibleGroup U c h) : f (t + w) ≤ 3 * f t - 2 * sInf S := by
    have hb := visibleComparison_balance U c h (x + t) (y + t) w w
    rw [visibleComparison_diagonal] at hb
    simp only [add_assoc] at hb
    change f (t + w) + (f (t + visibleMarker U c h w) +
      f (t + visibleMarker U c h (visibleMarker U c h w))) = 3 * f t + 3 * 0 at hb
    linarith [hm (t + visibleMarker U c h w),
      hm (t + visibleMarker U c h (visibleMarker U c h w))]
  have heq (s : visibleGroup U c h) : f s = sInf S := by
    have hlow : (f s + 2 * sInf S) / 3 ≤ sInf S := by
      apply le_csInf hne
      rintro _ ⟨t, rfl⟩
      have ht := hstep t (s - t)
      have he : t + (s - t) = s := by abel
      rw [he] at ht
      linarith
    exact le_antisymm (by linarith) (hm s)
  have hz := (heq z).trans (heq 0).symm
  simpa only [f, add_zero] using hz

/-- The squared-size candidate on the actual visible group. -/
def visibleEnergy {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x : visibleGroup U c h) : ℝ :=
  visibleComparison U c h x 0

section SquaredGeometry
variable {M : Type*} [MulOneClass M]
variable (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
local notation "A" => visibleGroup U c h
local notation "T" => visibleMarker U c h
local notation "f" => visibleEnergy U c h

private theorem energy_zero : f 0 = 0 := visibleComparison_diagonal U c h 0
private theorem energy_nonneg (x : A) : 0 ≤ f x := visibleComparison_nonneg U c h x 0

private theorem comparison_energy (x y : A) : visibleComparison U c h x y = f (x - y) := by
  have ht := raw_visible_translation_invariant U c h x y (-y)
  simpa only [add_neg_cancel, sub_eq_add_neg, visibleEnergy] using ht.symm

private theorem energy_balance (x y : A) :
    f (x + y) + f (x + T y) + f (x + T (T y)) = 3 * f x + 3 * f y := by
  have hb := visibleComparison_balance U c h x 0 y 0
  simpa only [map_zero, add_zero, visibleEnergy] using hb

/-- The actual visible squared-size function has an integer quadratic-map realization. -/
theorem raw_visible_quadratic :
    ∃ Q : QuadraticMap ℤ A ℝ, (∀ x, Q x = f x) ∧
      ∀ x y, visibleComparison U c h x y = Q (x - y) := by
  obtain ⟨Q, hQ⟩ :=
    (D5.S3.QuadraticForms.ThreeWayBalance.three_way_quadratic_structure
      T f (energy_nonneg U c h) (energy_balance U c h)).2.2.2.2
  exact ⟨Q, hQ, fun x y => (comparison_energy U c h x y).trans (hQ (x-y)).symm⟩
end SquaredGeometry


/-- A complete minimal model on the original magma; no factorization is assumed. -/
structure RawHilbertRepresentation {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) where
  carrier : Type v
  [normed : NormedAddCommGroup carrier]
  [innerProduct : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]
  label : M → carrier
  unit : label 1 = 0
  product : ∀ a b, label (a * b) = label a + label b
  phase : ∀ a, label (U a) = omega • label a
  distance : ∀ a b, c a b = ‖label a - label b‖ ^ 2
  minimal : (Submodule.span ℂ (Set.range label)).topologicalClosure = ⊤

attribute [instance] RawHilbertRepresentation.normed RawHilbertRepresentation.innerProduct
  RawHilbertRepresentation.complete

private def groupModel {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    HilbertRepresentation.{u, u} (visibleMarker U c h) (visibleEnergy U c h) :=
  Classical.choice ((three_way_hilbert_characterization.{u, u, u}
    (visibleMarker U c h) (visibleEnergy U c h) (energy_nonneg U c h)).1.mp
      (energy_balance U c h))

private theorem original_distance {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    (R : HilbertRepresentation.{u, v} (visibleMarker U c h) (visibleEnergy U c h)) (a b : M) :
    c a b = ‖R.label (visibleLabel U c h a) - R.label (visibleLabel U c h b)‖ ^ 2 := by
  rw [← visibleComparison_label U c h a b, comparison_energy, R.normSq, map_sub]

private def originalModel {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    (R : HilbertRepresentation.{u, v} (visibleMarker U c h) (visibleEnergy U c h)) :
    RawHilbertRepresentation.{u, v} U c where
  carrier := R.carrier
  label a := R.label (visibleLabel U c h a)
  unit := by rw [show visibleLabel U c h (1 : M) = 0 from Subtype.ext (gamma_one c), map_zero]
  product a b := by rw [visibleLabel_mul, map_add]
  phase a := by rw [visibleLabel_marker, R.phase]
  distance := original_distance U c h R
  minimal := by
    have he : Set.range (fun a => R.label (visibleLabel U c h a)) = Set.range R.label :=
      Set.range_comp R.label (visibleLabel U c h) |>.trans
        (by rw [Set.range_eq_univ.mpr (visibleLabel_surjective U c h), Set.image_univ])
    rw [he]
    exact R.minimal

private theorem rawLabel_balance {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (hU : U 1 = 1)
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (F : M → H) (hprod : ∀ a b, F (a*b) = F a + F b)
    (hphase : ∀ a, F (U a) = omega • F a)
    (hdist : ∀ a b, c a b = ‖F a - F b‖ ^ 2) : RawBalance U c := by
  let T : H →+ H :=
    (omega • (LinearMap.id : H →ₗ[ℂ] H)).toAddMonoidHom
  let R : HilbertRepresentation T (fun x : H => ‖x‖ ^ 2) :=
    { carrier := H
      label := AddMonoidHom.id _
      normSq := fun _ => rfl
      phase := fun _ => rfl
      minimal := by
        simp only [AddMonoidHom.coe_id, Set.range_id, Submodule.span_univ]
        exact top_unique (Submodule.le_topologicalClosure _) }
  have hb := (three_way_hilbert_characterization.{v, v, v} T (fun x : H => ‖x‖ ^ 2)
    (fun x => sq_nonneg ‖x‖)).2.1 R
  refine ⟨hU, fun a b => by rw [hdist]; positivity,
    fun a => by simp [hdist], ?_⟩
  intro a b d e
  have he (a b d e : M) :
      F (a*d) - F (b*e) =
        (F a - F b) + (F d - F e) := by
    rw [hprod, hprod]; abel
  simp only [hdist, he, hphase, ← smul_sub, smul_smul]
  simpa only [T, LinearMap.toAddMonoidHom_coe, LinearMap.smul_apply,
    LinearMap.id_apply, smul_smul] using hb (F a - F b) (F d - F e)

private theorem rawModel_balance {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (hU : U 1 = 1)
    (S : RawHilbertRepresentation.{u, v} U c) : RawBalance U c :=
  rawLabel_balance U c hU S.carrier S.label S.product S.phase S.distance

private theorem visible_label_zero_of_model_zero {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    (R : HilbertRepresentation.{u, v} (visibleMarker U c h) (visibleEnergy U c h))
    (a b : M) (he : R.label (visibleLabel U c h a) = R.label (visibleLabel U c h b)) :
    gamma c a = gamma c b := by
  have hl (z : M) : c a z = c b z := by
    rw [original_distance U c h R, original_distance U c h R, he]
  have hr (z : M) : c z a = c z b := by
    rw [original_distance U c h R, original_distance U c h R, he]
  have hq : q c a = q c b := hl 1
  have hrr : r c a = r c b := hr 1
  have hv : beta c a = beta c b := by
    apply sub_eq_zero.mp
    apply quotient_joint_nondegenerate c (h.diagonal 1)
    · intro z
      rw [map_sub, LinearMap.sub_apply, quotientForm_beta c (h.diagonal 1),
        quotientForm_beta c (h.diagonal 1)]
      simp only [kernel, hq, hl z, sub_self]
    · intro z
      rw [map_sub, quotientForm_beta c (h.diagonal 1), quotientForm_beta c (h.diagonal 1)]
      simp only [kernel, hrr, hr z, sub_self]
  exact congrArg (W c).mkQ hv

private theorem visible_energy_definite {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x : visibleGroup U c h) :
    visibleEnergy U c h x = 0 ↔ x = 0 := by
  let R := groupModel U c h
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := visibleLabel_surjective U c h x
    have hz : visibleLabel U c h (1 : M) = 0 := Subtype.ext (gamma_one c)
    have he : R.label (visibleLabel U c h a) = R.label (visibleLabel U c h 1) := by
      rw [hz, map_zero]
      have hn := hx
      rw [R.normSq] at hn
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    apply Subtype.ext
    exact (visible_label_zero_of_model_zero U c h R a 1 he).trans (gamma_one c)
  · rintro rfl
    exact energy_zero U c h

private theorem raw_zero_comparison_iff {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b : M) :
    c a b = 0 ↔ gamma c a = gamma c b := by
  rw [← visibleComparison_label U c h a b, comparison_energy, visible_energy_definite,
    sub_eq_zero]
  exact Subtype.ext_iff

private theorem model_constant_on_fibres {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    (S : RawHilbertRepresentation.{u, v} U c) (a b : M)
    (he : gamma c a = gamma c b) : S.label a = S.label b := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  rw [← S.distance]
  exact (raw_zero_comparison_iff U c h a b).mpr he

private def factoredModel {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    (S : RawHilbertRepresentation.{u, v} U c) :
    HilbertRepresentation.{u, v} (visibleMarker U c h) (visibleEnergy U c h) where
  carrier := S.carrier
  label :=
    { toFun x := S.label (originalLabel U c h x)
      map_zero' := by
        rw [model_constant_on_fibres U c h S _ 1 (by
          rw [originalLabel_spec, gamma_one]; rfl), S.unit]
      map_add' x y := by
        rw [model_constant_on_fibres U c h S _
          (originalLabel U c h x * originalLabel U c h y) (by
            rw [gamma_mul, originalLabel_spec, originalLabel_spec, originalLabel_spec]; rfl), S.product] }
  normSq x := by
    change c (originalLabel U c h x) (originalLabel U c h 0) =
      ‖S.label (originalLabel U c h x)‖ ^ 2
    rw [S.distance, model_constant_on_fibres U c h S (originalLabel U c h 0) 1 (by
      rw [originalLabel_spec, gamma_one]; rfl), S.unit, sub_zero]
  phase x := by
    change S.label (originalLabel U c h (visibleMarker U c h x)) =
      omega • S.label (originalLabel U c h x)
    rw [model_constant_on_fibres U c h S _ (U (originalLabel U c h x)) (by
      rw [gamma_marker, originalLabel_spec, originalLabel_spec]; rfl), S.phase]
  minimal := by
    change (Submodule.span ℂ (Set.range (fun x => S.label (originalLabel U c h x)))).topologicalClosure = ⊤
    have he : Set.range (fun x => S.label (originalLabel U c h x)) = Set.range S.label := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
      · rintro ⟨a, rfl⟩
        refine ⟨visibleLabel U c h a, ?_⟩
        exact model_constant_on_fibres U c h S _ a (originalLabel_spec U c h _)
    rw [he]
    exact S.minimal

/-- The complete Hilbert criterion on the original unital magma, with unique minimal models. -/
private theorem raw_hilbert_criterion {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (hU : U 1 = 1) :
    (RawBalance U c ↔ Nonempty (RawHilbertRepresentation.{u, u} U c)) ∧
    (∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (F : M → H), (∀ a b, F (a*b) = F a + F b) →
      (∀ a, F (U a) = omega • F a) →
      (∀ a b, c a b = ‖F a - F b‖ ^ 2) → RawBalance U c) ∧
    (∀ (h : RawBalance U c) (S : RawHilbertRepresentation.{u, v} U c)
      (T : RawHilbertRepresentation.{u, w} U c),
      ∃! e : S.carrier ≃ₗᵢ[ℂ] T.carrier, ∀ a, e (S.label a) = T.label a) := by
  refine ⟨⟨fun h => ⟨originalModel U c h (groupModel U c h)⟩,
    fun ⟨S⟩ => rawModel_balance U c hU S⟩,
    fun H _ _ _ F hprod hphase hdist => rawLabel_balance U c hU H F hprod hphase hdist, ?_⟩
  intro h S T
  obtain ⟨e, he, hu⟩ :=
    (three_way_hilbert_characterization.{u, v, w} (visibleMarker U c h) (visibleEnergy U c h)
      (energy_nonneg U c h)).2.2 (factoredModel U c h S) (factoredModel U c h T)
  refine ⟨e, ?_, ?_⟩
  · intro a
    have hx := he (visibleLabel U c h a)
    change e (S.label (originalLabel U c h (visibleLabel U c h a))) =
      T.label (originalLabel U c h (visibleLabel U c h a)) at hx
    rw [model_constant_on_fibres U c h S _ a
      (originalLabel_spec U c h (visibleLabel U c h a)),
      model_constant_on_fibres U c h T _ a
      (originalLabel_spec U c h (visibleLabel U c h a))] at hx
    exact hx
  · intro e' he'
    apply hu
    intro x
    obtain ⟨a, rfl⟩ := visibleLabel_surjective U c h x
    change e' (S.label (originalLabel U c h (visibleLabel U c h a))) =
      T.label (originalLabel U c h (visibleLabel U c h a))
    rw [model_constant_on_fibres U c h S _ a (originalLabel_spec U c h _),
      model_constant_on_fibres U c h T _ a (originalLabel_spec U c h _)]
    exact he' a


/-- The actual Eisenstein integer subring of the complex numbers. -/
abbrev Eisenstein := Algebra.adjoin ℤ ({omega} : Set ℂ)

private theorem model_image_smul {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    (R : HilbertRepresentation.{u, v} (visibleMarker U c h) (visibleEnergy U c h))
    (r : ℂ) (hr : r ∈ Eisenstein) :
    ∀ z ∈ Set.range R.label, r • z ∈ Set.range R.label := by
  induction hr using Algebra.adjoin_induction with
  | mem r hr =>
      have he : r = omega := Set.mem_singleton_iff.mp hr
      subst r
      rintro z ⟨x, rfl⟩
      exact ⟨visibleMarker U c h x, R.phase x⟩
  | algebraMap r =>
      rintro z ⟨x, rfl⟩
      refine ⟨r • x, ?_⟩
      change R.label (r • x) = (r : ℂ) • R.label x
      rw [map_zsmul, Int.cast_smul_eq_zsmul]
  | add r s _ _ hr hs =>
      intro z hz
      obtain ⟨x, hx⟩ := hr z hz
      obtain ⟨y, hy⟩ := hs z hz
      exact ⟨x+y, by rw [map_add, hx, hy, add_smul]⟩
  | mul r s _ _ hr hs =>
      intro z hz
      simpa only [mul_smul] using hr (s • z) (hs z hz)

/-- The actual label image, closed under precisely the generated integer scalars. -/
def visibleImage {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    (R : HilbertRepresentation.{u, v} (visibleMarker U c h) (visibleEnergy U c h)) :
    Submodule Eisenstein R.carrier where
  carrier := Set.range R.label
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x+y, map_add _ x y⟩
  smul_mem' r z hz := model_image_smul U c h R r.val r.property z hz

private def imageAddEquiv {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    (R : HilbertRepresentation.{u, v} (visibleMarker U c h) (visibleEnergy U c h)) :
    visibleGroup U c h ≃+ visibleImage U c h R :=
  AddEquiv.ofBijective
    (show visibleGroup U c h →+ visibleImage U c h R from
    { toFun x := ⟨R.label x, ⟨x, rfl⟩⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' x y := Subtype.ext (map_add _ x y) })
    ⟨by
      intro x y he
      have hz : visibleEnergy U c h (x-y) = 0 := by
        rw [R.normSq, map_sub, show R.label x = R.label y from congrArg Subtype.val he,
          sub_self, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
      exact sub_eq_zero.mp ((visible_energy_definite U c h _).mp hz),
    by rintro ⟨z, x, rfl⟩; exact ⟨x, rfl⟩⟩

/-- The equivalence relation is the original zero comparison, in its original direction. -/
def zeroComparisonSetoid {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) : Setoid M where
  r a b := c a b = 0
  iseqv :=
    { refl a := h.diagonal a
      symm := by
        intro a b hab
        exact (raw_zero_comparison_iff U c h b a).mpr
          ((raw_zero_comparison_iff U c h a b).mp hab).symm
      trans := by
        intro a b d hab hbd
        exact (raw_zero_comparison_iff U c h a d).mpr
          (((raw_zero_comparison_iff U c h a b).mp hab).trans
            ((raw_zero_comparison_iff U c h b d).mp hbd)) }

abbrev VisibleQuotient {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :=
  Quotient (zeroComparisonSetoid U c h)

private def quotientEquiv {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    VisibleQuotient U c h ≃ visibleGroup U c h :=
  Equiv.ofBijective
    (Quotient.lift (visibleLabel U c h) (by
      intro a b hab
      exact Subtype.ext ((raw_zero_comparison_iff U c h a b).mp hab)))
    ⟨by
      intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro a b he
      exact Quotient.sound ((raw_zero_comparison_iff U c h a b).mpr (congrArg Subtype.val he)),
    by
      intro x
      obtain ⟨a, rfl⟩ := visibleLabel_surjective U c h x
      exact ⟨Quotient.mk _ a, rfl⟩⟩

instance quotientAddCommGroup {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    AddCommGroup (VisibleQuotient U c h) := (quotientEquiv U c h).addCommGroup

private def quotientAddEquiv {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    VisibleQuotient U c h ≃+ visibleGroup U c h where
  toEquiv := quotientEquiv U c h
  map_add' x y := (quotientEquiv U c h).apply_symm_apply _

private def quotientImageEquiv {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    VisibleQuotient U c h ≃+ visibleImage U c h (groupModel U c h) :=
  (quotientAddEquiv U c h).trans (imageAddEquiv U c h (groupModel U c h))

instance quotientModule {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    Module Eisenstein (VisibleQuotient U c h) := (quotientImageEquiv U c h).module Eisenstein

/-- The generator is the actual complex cube root inside its generated integer subring. -/
def omegaScalar : Eisenstein := ⟨omega, Algebra.subset_adjoin (Set.mem_singleton omega)⟩

/-- The source's complete visible algebra on the actual zero-comparison quotient. -/
private theorem raw_visible_algebra {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    (∀ a b, c a b = 0 ↔ gamma c a = gamma c b) ∧
    (∀ a b d e, c a b = 0 → c d e = 0 → c (a*d) (b*e) = 0) ∧
    (∀ a b, c a b = 0 → c (U a) (U b) = 0) ∧
    (∀ a b d, c ((a*b)*d) (a*(b*d)) = 0) ∧
    (∀ a b, c (a*b) (b*a) = 0) ∧
    (∀ a, c (U (U (U a))) a = 0) ∧
    (∀ a, (Quotient.mk _ (U a * U (U a)) : VisibleQuotient U c h) = -Quotient.mk _ a) ∧
    (∀ a b, (Quotient.mk _ (a*b) : VisibleQuotient U c h) = Quotient.mk _ a + Quotient.mk _ b) ∧
    (∃ e : VisibleQuotient U c h ≃ₗ[Eisenstein] visibleImage U c h (groupModel U c h),
      ∀ a, (e (Quotient.mk _ a)).val = (groupModel U c h).label (visibleLabel U c h a)) ∧
    (∀ a, (Quotient.mk _ (U a) : VisibleQuotient U c h) = omegaScalar • Quotient.mk _ a) ∧
    (∀ (r : Eisenstein) (x : VisibleQuotient U c h), r ≠ 0 → r • x = 0 → x = 0) := by
  refine ⟨raw_zero_comparison_iff U c h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b d e hab hde
    apply (raw_zero_comparison_iff U c h _ _).mpr
    rw [gamma_mul, gamma_mul, (raw_zero_comparison_iff U c h _ _).mp hab,
      (raw_zero_comparison_iff U c h _ _).mp hde]
  · intro a b hab
    apply (raw_zero_comparison_iff U c h _ _).mpr
    rw [gamma_marker U c h, gamma_marker U c h,
      (raw_zero_comparison_iff U c h _ _).mp hab]
  · intro a b d
    apply (raw_zero_comparison_iff U c h _ _).mpr
    simp only [gamma_mul, add_assoc]
  · intro a b
    apply (raw_zero_comparison_iff U c h _ _).mpr
    simp only [gamma_mul, add_comm]
  · intro a
    apply (raw_zero_comparison_iff U c h _ _).mpr
    exact congrArg (W c).mkQ (marker_period_three_on_beta U c h a)
  · intro a
    apply (quotientAddEquiv U c h).injective
    rw [map_neg]
    change visibleLabel U c h (U a * U (U a)) = -visibleLabel U c h a
    exact Subtype.ext (gamma_inverse_label U c h a)
  · intro a b
    apply (quotientAddEquiv U c h).injective
    rw [map_add]
    change visibleLabel U c h (a*b) = visibleLabel U c h a + visibleLabel U c h b
    exact visibleLabel_mul U c h a b
  · exact ⟨(quotientImageEquiv U c h).linearEquiv Eisenstein, fun _ => rfl⟩
  · intro a
    let e := (quotientImageEquiv U c h).linearEquiv Eisenstein
    apply e.injective
    rw [map_smul]
    apply Subtype.ext
    change (groupModel U c h).label (visibleLabel U c h (U a)) =
      omega • (groupModel U c h).label (visibleLabel U c h a)
    rw [visibleLabel_marker, (groupModel U c h).phase]
  · intro r x hr hx
    apply (quotientImageEquiv U c h).injective
    apply Subtype.ext
    let e := (quotientImageEquiv U c h).linearEquiv Eisenstein
    have he := congrArg (fun z => (e z).val) hx
    rw [map_smul, map_zero] at he
    change (r : ℂ) • (e x).val = 0 at he
    have hrC : (r : ℂ) ≠ 0 := by intro he; apply hr; exact Subtype.ext he
    have hz := (smul_eq_zero.mp he).resolve_left hrC
    change (e x).val = (e 0).val
    rw [map_zero]
    exact hz

/-- The whole original Hilbert classification, including all visible-algebra clauses. -/
theorem raw_hilbert_characterization {M : Type u} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (hU : U 1 = 1) :
    ((RawBalance U c ↔ Nonempty (RawHilbertRepresentation.{u, u} U c)) ∧
    (∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (F : M → H), (∀ a b, F (a*b) = F a + F b) →
      (∀ a, F (U a) = omega • F a) →
      (∀ a b, c a b = ‖F a - F b‖ ^ 2) → RawBalance U c) ∧
    (∀ (h : RawBalance U c) (S : RawHilbertRepresentation.{u, v} U c)
      (T : RawHilbertRepresentation.{u, w} U c),
      ∃! e : S.carrier ≃ₗᵢ[ℂ] T.carrier, ∀ a, e (S.label a) = T.label a)) ∧
    ∀ h : RawBalance U c,
    ((∀ a b, c a b = 0 ↔ gamma c a = gamma c b) ∧
    (∀ a b d e, c a b = 0 → c d e = 0 → c (a*d) (b*e) = 0) ∧
    (∀ a b, c a b = 0 → c (U a) (U b) = 0) ∧
    (∀ a b d, c ((a*b)*d) (a*(b*d)) = 0) ∧
    (∀ a b, c (a*b) (b*a) = 0) ∧
    (∀ a, c (U (U (U a))) a = 0) ∧
    (∀ a, (Quotient.mk _ (U a * U (U a)) : VisibleQuotient U c h) = -Quotient.mk _ a) ∧
    (∀ a b, (Quotient.mk _ (a*b) : VisibleQuotient U c h) = Quotient.mk _ a + Quotient.mk _ b) ∧
    (∃ e : VisibleQuotient U c h ≃ₗ[Eisenstein] visibleImage U c h (groupModel U c h),
      ∀ a, (e (Quotient.mk _ a)).val = (groupModel U c h).label (visibleLabel U c h a)) ∧
    (∀ a, (Quotient.mk _ (U a) : VisibleQuotient U c h) = omegaScalar • Quotient.mk _ a) ∧
    (∀ (r : Eisenstein) (x : VisibleQuotient U c h), r ≠ 0 → r • x = 0 → x = 0)) ∧
    (∃ Q : QuadraticMap ℤ (visibleGroup U c h) ℝ,
      (∀ x, Q x = visibleEnergy U c h x) ∧
      ∀ x y, visibleComparison U c h x y = Q (x-y)) := by
  exact ⟨raw_hilbert_criterion U c hU,
    fun h => ⟨raw_visible_algebra U c h, raw_visible_quadratic U c h⟩⟩

end D5.S3.Quantum.Completion.RawAnchoredRadicalDescent
