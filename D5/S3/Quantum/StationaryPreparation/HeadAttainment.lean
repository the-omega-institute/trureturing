/- GID: D5/S3/Quantum/StationaryPreparation/HeadAttainment
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/HeadAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One stationary isometry exactly prepares every finite occupation state at minimum memory dimension. -/

import D5.S3.Quantum.StationaryPreparation.HeadGram
import D5.S3.Quantum.Algebra.GramUnitaryExtension

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open D5.S3.Quantum.StationaryPreparation.PhysicalGram
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
namespace D5.S3.Quantum.StationaryPreparation.HeadAttainment
open D5.S3.Quantum.StationaryPreparation.HeadGram
variable {σ : Type*} [Fintype σ] [DecidableEq σ] [Nonempty σ]

-- Exact physical attainment; the lower bound is applied only after constructing P.
theorem stationary_attainment (a : σ → ℕ) :
    ∃ h : σ,
    letI : NormedAddCommGroup (memory a h) := (memory a h).normedAddCommGroup
    letI : InnerProductSpace ℂ (memory a h) := (memory a h).innerProductSpace
    ∃ _P : PhysicalPreparation (H := memory a h) a,
      Module.finrank ℂ (memory a h) = (∏ i, (a i + 1)) - Finset.univ.sup a := by
  classical
  obtain ⟨h, _, hh⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty a
  refine ⟨h, ?_⟩
  letI : NormedAddCommGroup (memory a h) := (memory a h).normedAddCommGroup
  letI : InnerProductSpace ℂ (memory a h) := (memory a h).innerProductSpace
  letI : FiniteDimensional ℂ (memory a h) := inferInstance
  have raw_inner (r s : Box a) : inner ℂ (raw h r) (raw h s) =
      (headKernel h (values r) (values s) : ℂ) := (head_gram_realization a h).1 r s
  have hrawmap : ∃ V : memory a h →ₗᵢ[ℂ] EuclideanSpace ℂ σ ⊗[ℂ] memory a h,
      ∀ r : Box a, r ≠ 0 → ∀ i : σ,
        letter V i (vector h r) = if 0 < (r i).val then vector h (lower r i) else 0 := by
    let I : Type _ :=  {r : Box a // r ≠ 0}
    let E : Type _ := ↥(memory a h)
    letI : NormedAddCommGroup E := (memory a h).normedAddCommGroup
    letI : InnerProductSpace ℂ E := (memory a h).innerProductSpace
    letI : FiniteDimensional ℂ E := inferInstanceAs (FiniteDimensional ℂ (memory a h))
    let F := EuclideanSpace ℂ I
    let T := PiLp 2 (fun _ : σ => E)
    letI : InnerProductSpace ℂ T := PiLp.innerProductSpace (fun _ : σ => E)
    let src : I → E := fun r => vector h r.val
    let dst : I → T := fun r => WithLp.toLp 2
      (fun i => if 0 < (r.val i).val then vector h (lower r.val i) else 0)
    have hvalues (r : I) : values r.val ≠ 0 := by
      intro hh
      apply r.property
      funext i
      apply Fin.ext
      exact congrFun hh i
    have hdecrease (r : Box a) (i : σ) :
        values (lower r i) = decrease (values r) i := by
      funext j
      by_cases hj : j = i
      · subst j
        simp [values, lower, sub, decrease]
      · simp [values, lower, sub, decrease, hj]
    have hcol (r s : I) : inner ℂ (src r) (src s) = inner ℂ (dst r) (dst s) := by
      change inner ℂ (raw h r.val) (raw h s.val) = _
      rw [raw_inner, PiLp.inner_apply]
      have he := (head_gram_realization a h).2.1 (values r.val) (values s.val) (hvalues r) (hvalues s)
      rw [he]
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      simp only [apply_ite, Complex.ofReal_zero]
      change (if 0 < (r.val i).val ∧ 0 < (s.val i).val then
        (headKernel h (decrease (values r.val) i) (decrease (values s.val) i) : ℂ) else 0) =
        inner ℂ (if 0 < (r.val i).val then vector h (lower r.val i) else 0)
          (if 0 < (s.val i).val then vector h (lower s.val i) else 0)
      by_cases hr : 0 < (r.val i).val <;> by_cases hs : 0 < (s.val i).val
      · simp only [hr, hs, and_self, if_true]
        change _ = inner ℂ (raw h (lower r.val i)) (raw h (lower s.val i))
        rw [raw_inner, hdecrease, hdecrease]
      all_goals simp [hr, hs]
    let blank : E →ₗᵢ[ℂ] T :=
      { toLinearMap :=
          { toFun := fun x => PiLp.single 2 h x
            map_add' := fun x y => PiLp.single_add 2 h
            map_smul' := by
              intro c x
              apply PiLp.ext
              intro i
              change (Pi.single h (c • x) : σ → E) i = c • (Pi.single h x : σ → E) i
              by_cases hi : i = h <;> simp [hi] }
        norm_map' := fun x => PiLp.norm_single 2 (fun _ : σ => E) h x }
    let b := stdOrthonormalBasis ℂ T
    let A : Matrix (Fin (Module.finrank ℂ T)) I ℂ := fun q r => b.repr (blank (src r)) q
    let B : Matrix (Fin (Module.finrank ℂ T)) I ℂ := fun q r => b.repr (dst r) q
    have hgram : B.conjTranspose * B = A.conjTranspose * A := by
      calc
        B.conjTranspose * B = Matrix.gram ℂ dst := (Matrix.gram_eq_conjTranspose_mul b dst).symm
        _ = Matrix.gram ℂ (fun r => blank (src r)) := by
          ext r s
          simp only [Matrix.gram_apply, LinearIsometry.inner_map_map]
          exact (hcol r s).symm
        _ = A.conjTranspose * A := Matrix.gram_eq_conjTranspose_mul b (fun r => blank (src r))
    obtain ⟨W, hW⟩ := D5.S3.Quantum.Algebra.GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq B A hgram
    let WI := D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.matrixIsometry
      (W : Matrix (Fin (Module.finrank ℂ T)) (Fin (Module.finrank ℂ T)) ℂ)
      (Matrix.mem_unitaryGroup_iff'.mp W.property)
    let U : E →ₗᵢ[ℂ] T := b.repr.symm.toLinearIsometry.comp
      (WI.comp (b.repr.toLinearIsometry.comp blank))
    have hb (r : I) : U (src r) = dst r := by
      apply b.repr.injective
      change b.repr (b.repr.symm (WI (b.repr (blank (src r))))) = b.repr (dst r)
      rw [LinearIsometryEquiv.apply_symm_apply]
      ext q
      have he := congrFun (congrFun hW q) r
      change (b.repr (dst r)) q =
        ∑ j, (W : Matrix (Fin (Module.finrank ℂ T)) (Fin (Module.finrank ℂ T)) ℂ) q j *
          (b.repr (blank (src r))) j at he
      change (∑ j, (W : Matrix (Fin (Module.finrank ℂ T)) (Fin (Module.finrank ℂ T)) ℂ) q j *
          (b.repr (blank (src r))) j) = (b.repr (dst r)) q
      exact he.symm
    refine ⟨(tensorCoordinates (σ := σ) (H := E)).symm.toLinearIsometry.comp U, ?_⟩
    intro r hr i
    have hh := congrArg (fun x : T => x i) (hb ⟨r, hr⟩)
    simpa [letter, LinearIsometry.comp_apply, LinearIsometryEquiv.apply_symm_apply,
      src, dst] using hh
  obtain ⟨V, hV⟩ := hrawmap
  let φ : Box a → memory a h := fun r => (realSqrt (M (values r) : ℝ))⁻¹ • vector h r
  have hMpos (b : σ → ℕ) : 0 < M b := Nat.multinomial_pos Finset.univ b
  have hMzero : M (0 : σ → ℕ) = 1 := by simp [M, mass]
  have hnorm (r : Box a) : ‖vector h r‖ = Real.sqrt (M (values r) : ℝ) := by
    have hh := congrArg Complex.re (raw_inner r r)
    simp only [headKernel, sameTail, implies_true, if_true,
      min_self, Complex.ofReal_re] at hh
    change RCLike.re (inner ℂ (raw h r) (raw h r)) = (M (values r) : ℝ) at hh
    rw [inner_self_eq_norm_sq (𝕜 := ℂ)] at hh
    change ‖raw h r‖ = _
    rw [← hh, Real.sqrt_sq (norm_nonneg _)]
  have hunit (r : Box a) : ‖φ r‖ = 1 := by
    have hp : 0 < Real.sqrt (M (values r) : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hMpos _)
    dsimp only [φ]
    rw [norm_smul, norm_inv, hnorm]
    simp only [realSqrt, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    exact inv_mul_cancel₀ (ne_of_gt hp)
  have profile_count (b : σ → ℕ) (i : σ) : (profile b).count i = b i := by
    simp [profile, Multiset.count_sum', Multiset.count_replicate]
  have hM (b : σ → ℕ) : M b = multiplicity (mass b) (profile b) := by
    rw [multiplicity_eq_factorial (profile b) (by simp [profile, mass])]
    simp only [profile_count]
    rfl
  have hprof (r : Box a) (i : σ) : profile (values (lower r i)) = (profile (values r)).erase i := by
    apply Multiset.ext.mpr
    intro j
    rw [profile_count]
    by_cases hj : j = i
    · subst j
      simp [values, lower, sub, Multiset.count_erase_self, profile_count]
    · simpa [values, lower, sub, hj, profile_count] using
        (Multiset.count_erase_of_ne hj (profile (values r))).symm
  have hrelation (r : Box a) (i : σ) (hi : 0 < (r i).val) :
      mass (values r) * M (values (lower r i)) = (r i).val * M (values r) := by
    have hp : 0 < mass (values r) := lt_of_lt_of_le hi
      (Finset.single_le_sum (f := values r) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    have hm : i ∈ profile (values r) := by rw [← Multiset.count_pos, profile_count]; exact hi
    have hc : (profile (values r)).card = mass (values r) := by simp [profile, mass]
    have hl : mass (values (lower r i)) = mass (values r) - 1 := by
      have he := congrArg Multiset.card (hprof r i)
      rw [Multiset.card_erase_of_mem hm, hc] at he
      simpa [profile, mass] using he
    have he := multiplicity_erase_mul (a := profile (values r))
      (n := mass (values r) - 1) (by rw [hc]; omega) i hm
    rw [Nat.sub_add_cancel hp, profile_count] at he
    rw [show values r i = (r i).val from rfl] at he
    simpa [hM, hl, hprof] using he
  have hstep : Step a V φ := by
    intro r hr i
    change tensorCoordinates (V ((realSqrt (M (values r) : ℝ))⁻¹ • vector h r)) i = _
    rw [map_smul, map_smul, PiLp.smul_apply]
    change (realSqrt (M (values r) : ℝ))⁻¹ • letter V i (vector h r) = _
    rw [hV r hr i]
    by_cases hi : 0 < (r i).val
    · rw [if_pos hi, if_pos hi]
      change (realSqrt (M (values r) : ℝ))⁻¹ • vector h (lower r i) =
        realSqrt ((r i).val / (mass (values r) : ℝ)) •
          ((realSqrt (M (values (lower r i)) : ℝ))⁻¹ • vector h (lower r i))
      rw [smul_smul]
      congr 1
      have hq : 0 < (mass (values r) : ℝ) := by
        exact_mod_cast lt_of_lt_of_le hi
          (Finset.single_le_sum (f := values r) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      have hp : 0 < (M (values r) : ℝ) := by exact_mod_cast hMpos _
      have hl : 0 < (M (values (lower r i)) : ℝ) := by exact_mod_cast hMpos _
      have he : (mass (values r) : ℝ) * M (values (lower r i)) =
          (r i).val * (M (values r) : ℝ) := by exact_mod_cast hrelation r i hi
      have hratio : ((r i).val : ℝ) / mass (values r) =
          (M (values (lower r i)) : ℝ) / M (values r) := by
        apply (div_eq_div_iff (ne_of_gt hq) (ne_of_gt hp)).mpr
        nlinarith [he]
      rw [hratio]
      simp only [realSqrt, div_eq_mul_inv]
      have hz : (Real.sqrt (M (values (lower r i)) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr hl).ne'
      field_simp
      rw [Real.sqrt_div (le_of_lt hl), Complex.ofReal_div]
    · simp [hi]
  have hwords := residual_word_formula a V φ hstep
  have htotal (w : List σ) : mass (counts w) = w.length := by
    have hc := Multiset.sum_count_eq_card (s := (Finset.univ : Finset σ))
      (m := (w : Multiset σ)) (fun _ _ => Finset.mem_univ _)
    simpa [mass, counts] using hc
  have heq (w : List σ) (hw : w.length = mass a) :
      (∀ i, w.count i ≤ a i) ↔ counts w = a := by
    constructor
    · intro hc
      have hsum : ∑ i, counts w i = ∑ i, a i := (htotal w).trans hw
      have hsame := (Finset.sum_eq_sum_iff_of_le (fun i _ => hc i)).mp hsum
      funext i
      exact hsame i (Finset.mem_univ i)
    · intro hc i
      exact (congrFun hc i).le
  have hout : emitted V (mass a) (φ (top a)) = sector a ⊗ₜ[ℂ] φ 0 := by
    unfold emitted
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin (mass a) → σ) ℂ).sum_repr (sector a)]
    simp only [TensorProduct.sum_tmul]
    apply Finset.sum_congr rfl
    intro w _
    rw [hwords (top a) (List.ofFn w) (by rw [show values (top a) = a from rfl]; simp only [List.length_ofFn, le_refl])]
    have hc : (∀ i, (List.ofFn w).count i ≤ (top a i).val) ↔ counts (List.ofFn w) = a :=
      heq _ (by simp)
    by_cases hw : counts (List.ofFn w) = a
    · rw [if_pos (hc.mpr hw)]
      have hz : sub (top a) (counts (List.ofFn w)) = 0 := by
        funext i
        apply Fin.ext
        simp [sub, top, hw]
      rw [hz]
      have hsqrt : realSqrt ((M (values (0 : Box a)) : ℝ) / M (values (top a))) =
          (realSqrt (M a : ℝ))⁻¹ := by
        have hzval : values (0 : Box a) = 0 := rfl
        have htval : values (top a) = a := rfl
        rw [hzval, htval, hMzero]
        simp [realSqrt, Real.sqrt_inv]
      rw [hsqrt]
      simp [sector, hw, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    · rw [if_neg (fun ht => hw (hc.mp ht))]
      simp [sector, hw]
  let P : PhysicalPreparation (H := memory a h) a :=
    { V := V
      initial := φ (top a)
      final := φ 0
      initial_unit := hunit _
      final_unit := hunit _
      output := hout }
  refine ⟨P, Nat.le_antisymm ?_ (physical_gram_from_exact_preparation a P).2.2.2⟩
  simpa only [hh] using (head_gram_realization a h).2.2.1
end D5.S3.Quantum.StationaryPreparation.HeadAttainment
