/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIISL2RootNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weyl and Hua reconstruction of finite-field root coordinates. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIISL2Projective
/-! Concrete A1 root-pair normalization toward PartII's Inn D Phi step.
Actual Weyl/torus incidences derive the field action. Hua's identity proves
multiplicativity in both characteristics; no field-action or coverage oracle.
The next arbitrary-root conjugacy obligation is separated explicitly. -/
open scoped MatrixGroups
set_option autoImplicit false
namespace NikolovSegal.PartIIA1RootSupply
universe u
variable {F : Type u} [Field F]
private theorem hua (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a*b ≠ 1) :
    a - (a⁻¹+(b⁻¹-a)⁻¹)⁻¹ = a^2*b := by
  have hdiff : b⁻¹-a ≠ 0 := by
    intro h
    have hh : b⁻¹ = a := sub_eq_zero.mp h
    apply hab
    rw [← hh,inv_mul_cancel₀ hb]
  have hsum : a⁻¹+(b⁻¹-a)⁻¹ ≠ 0 := by
    intro h
    have hh := h
    field_simp at hh
    exact one_ne_zero (by linear_combination hh)
  field_simp
  ring

theorem root_inverse_addEquiv_ring [Finite F] (f : F ≃+ F)
    (h1 : f 1 = 1) (hinv : ∀ a, f a⁻¹ = (f a)⁻¹) :
    ∃ phi : RingAut F, ∀ a, phi a = f a := by
  have hzero : ∀ a, f a = 0 ↔ a = 0 := by
    intro a
    exact f.map_eq_zero_iff
  have htriple : ∀ a b, f (a^2*b) = (f a)^2*f b := by
    intro a b
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    by_cases hab : a*b = 1
    · have hba : b = a⁻¹ := by
        apply mul_left_cancel₀ ha
        rw [hab,mul_inv_cancel₀ ha]
      rw [hba,hinv]
      have hfa : f a ≠ 0 := by intro hf; exact ha ((hzero a).mp hf)
      simp [pow_two,mul_assoc,ha,hfa]
    · have hfa : f a ≠ 0 := by intro hf; exact ha ((hzero a).mp hf)
      have hfb : f b ≠ 0 := by intro hf; exact hb ((hzero b).mp hf)
      have hfab : f a*f b ≠ 1 := by
        intro h
        have hh : f b = (f a)⁻¹ := by
          apply mul_left_cancel₀ hfa
          rw [h,mul_inv_cancel₀ hfa]
        have hba : b = a⁻¹ := f.injective (by rw [hinv]; exact hh)
        exact hab (by rw [hba,mul_inv_cancel₀ ha])
      have hh := congrArg f (hua a b ha hb hab)
      simp only [map_sub,map_add,hinv] at hh
      rw [hua (f a) (f b) hfa hfb hfab] at hh
      exact hh.symm
  have hsq : ∀ a, f (a^2) = (f a)^2 := by
    intro a
    simpa only [mul_one,h1] using htriple a 1
  have hmul : ∀ a b, f (a*b) = f a*f b := by
    intro a b
    by_cases htwo : (2:F) = 0
    · have hsqinj : Function.Injective (fun x : F => x^2) := by
        intro x y hxy
        change x^2=y^2 at hxy
        have hh : (x-y)^2 = 0 := by
          calc
            (x-y)^2 = x^2-y^2-(2:F)*y*(x-y) := by ring
            _ = 0 := by rw [hxy,htwo]; ring
        exact sub_eq_zero.mp (sq_eq_zero_iff.mp hh)
      obtain ⟨x,hx⟩ := (Finite.surjective_of_injective hsqinj) a
      rw [← hx,htriple,hsq]
    · have hpoly : (a+b)^2 = a^2+a*b+a*b+b^2 := by ring
      have hh := congrArg f hpoly
      simp only [map_add,hsq] at hh
      have heq : (2:F)*(f (a*b)-f a*f b) = 0 := by linear_combination -hh
      exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left htwo)
  refine ⟨{f with map_mul' := hmul},fun a => rfl⟩


private theorem upper_injective : Function.Injective (upper (F := F)) := by
  intro t s h
  have hh := congrArg (fun g : SL(2,F) => g.val 0 1) h
  simpa [upper,Matrix.SpecialLinearGroup.transvection_coe] using hh
private theorem lower_injective : Function.Injective (lower (F := F)) := by
  intro t s h
  have hh := congrArg (fun g : SL(2,F) => g.val 1 0) h
  simpa [lower,Matrix.SpecialLinearGroup.transvection_coe] using hh

def a1Weyl (x : F) (hx : x ≠ 0) : SL(2,F) :=
  ⟨!![0,x;-x⁻¹,0],by simp [Matrix.det_fin_two,hx]⟩

theorem a1Weyl_product (x : F) (hx : x ≠ 0) :
    upper x*lower (-x⁻¹)*upper x = a1Weyl x hx := by
  apply Subtype.ext
  change (upper x).val*(lower (-x⁻¹)).val*(upper x).val = (a1Weyl x hx).val
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [upper,lower,a1Weyl,Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  all_goals field_simp [hx]
  all_goals try ring
  all_goals simp

theorem a1Weyl_upper (x : F) (hx : x ≠ 0) (t : F) :
    MulAut.conj (a1Weyl x hx) (upper t) = lower (-(x⁻¹)^2*t) := by
  simp only [MulAut.conj_apply]
  apply Subtype.ext
  change (a1Weyl x hx).val*(upper t).val*Matrix.adjugate (a1Weyl x hx).val = _
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [upper,lower,a1Weyl,Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,hx]
  all_goals ring

private theorem zero_diagonal_of_swaps (G : SL(2,F)) (t s : F) (ht : t ≠ 0)
    (h : MulAut.conj G (upper t) = lower s) : G 0 0 = 0 := by
  have hh := congrArg (fun g : SL(2,F) => g.val 0 1) h
  change (G.val*(upper t).val*Matrix.adjugate G.val) 0 1 = (lower s).val 0 1 at hh
  rw [Matrix.adjugate_fin_two] at hh
  simp [upper,lower,Matrix.SpecialLinearGroup.transvection_coe,Matrix.mul_apply,
    Fin.sum_univ_two] at hh
  have hp : (G 0 0)^2*t = 0 := by linear_combination hh
  exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hp).resolve_right ht)

private theorem root_pair_semilinear [Finite F] (beta : MulAut SL(2,F))
    (f g : F ≃+ F) (hu : ∀ t, beta (upper t) = upper (f t))
    (hl : ∀ t, beta (lower t) = lower (g t)) :
    ∃ a : Fˣ, ∃ phi : RingAut F, (∀ t, f t = (a:F)*phi t) ∧
      (∀ t, g t = (↑a⁻¹:F)*phi t) := by
  have hf1 : f 1 ≠ 0 := by intro h; exact one_ne_zero (f.injective (by simpa using h))
  have hc : ∀ W t, beta (MulAut.conj W (upper t)) =
      MulAut.conj (beta W) (upper (f t)) := by
    intro W t
    simp only [MulAut.conj_apply,map_mul,map_inv,hu]
  have hfg : ∀ x, x ≠ 0 → f x*g x⁻¹ = 1 := by
    intro x hx
    have hswap : MulAut.conj (beta (a1Weyl x hx)) (upper (f 1)) = lower (g (-(x⁻¹)^2)) := by
      rw [← hc,a1Weyl_upper,mul_one,hl]
    have hz := zero_diagonal_of_swaps (beta (a1Weyl x hx)) _ _ hf1 hswap
    have hb : beta (a1Weyl x hx) = upper (f x)*lower (-(g x⁻¹))*upper (f x) := by
      rw [← a1Weyl_product]
      simp only [map_mul,hu,hl,map_neg]
    rw [hb] at hz
    change ((upper (f x)).val*(lower (-(g x⁻¹))).val*(upper (f x)).val) 0 0 = 0 at hz
    simp [upper,lower,Matrix.SpecialLinearGroup.transvection_coe,Matrix.mul_apply,
      Matrix.vecMul,dotProduct,Fin.sum_univ_two] at hz
    linear_combination -hz
  have hg1 : g 1 = (f 1)⁻¹ := by
    apply mul_left_cancel₀ hf1
    simpa only [inv_one,mul_inv_cancel₀ hf1] using hfg 1 one_ne_zero
  have hbw : beta (a1Weyl 1 one_ne_zero) = a1Weyl (f 1) hf1 := by
    rw [← a1Weyl_product]
    simp only [map_mul,hu,hl,map_neg,inv_one,hg1]
    exact a1Weyl_product _ hf1
  have hg : ∀ t, g t = ((f 1)⁻¹)^2*f t := by
    intro t
    have hh := hc (a1Weyl 1 one_ne_zero) t
    rw [a1Weyl_upper,inv_one,one_pow,neg_one_mul,hl,map_neg,hbw,a1Weyl_upper] at hh
    have h := lower_injective hh
    linear_combination -h
  let a : Fˣ := Units.mk0 (f 1) hf1
  let fn : F ≃+ F :=
    { toFun := fun t => (f 1)⁻¹*f t
      invFun := fun t => f.symm (f 1*t)
      left_inv := by intro t; simp [mul_assoc,hf1]
      right_inv := by intro t; simp [mul_assoc,hf1]
      map_add' := by intro t s; simp [map_add,mul_add] }
  have hfn1 : fn 1 = 1 := by dsimp [fn]; exact inv_mul_cancel₀ hf1
  have hfninv : ∀ t, fn t⁻¹ = (fn t)⁻¹ := by
    intro t
    by_cases ht : t = 0
    · simp [ht]
    have hft : f t ≠ 0 := by intro h; exact ht (f.injective (by simpa using h))
    have hp : fn t*fn t⁻¹ = 1 := by
      change ((f 1)⁻¹*f t)*((f 1)⁻¹*f t⁻¹)=1
      calc
        _ = f t*(((f 1)⁻¹)^2*f t⁻¹) := by ring
        _ = 1 := by rw [← hg]; exact hfg t ht
    have hnt : fn t ≠ 0 := by dsimp [fn]; exact mul_ne_zero (inv_ne_zero hf1) hft
    apply mul_left_cancel₀ hnt
    rw [hp,mul_inv_cancel₀ hnt]
  obtain ⟨phi,hphi⟩ := root_inverse_addEquiv_ring fn hfn1 hfninv
  refine ⟨a,phi,?_,?_⟩
  · intro t
    rw [hphi]
    change f t = f 1*((f 1)⁻¹*f t)
    rw [← mul_assoc,mul_inv_cancel₀ hf1,one_mul]
  · intro t
    rw [hphi,hg]
    change ((f 1)⁻¹)^2*f t = (f 1)⁻¹*((f 1)⁻¹*f t)
    ring

/-- The root laws needed by the scalar theorem are DERIVED from actual
additive upper/lower root coordinate bijections, including field multiplication
via Hua's identity in either characteristic. No semilinearity is assumed. -/
theorem actual_root_pair_SL2_scalar_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (beta : Fin (4*M) → MulAut SL(2,F)) (e : Fin (4*M) → ℕ)
    (f g : Fin (4*M) → F ≃+ F)
    (hu : ∀ j t, beta j (upper t) = upper (f j t))
    (hl : ∀ j t, beta j (lower t) = lower (g j t)) :
    PartIIScalarProductInput q (4*M) beta e := by
  classical
  choose a phi hf hg using fun j => root_pair_semilinear (beta j) (f j) (g j) (hu j) (hl j)
  apply actual_normalized_SL2_scalar_product hq hM hF beta e phi phi
    (fun j => (a j:F)) (fun j => (↑(a j)⁻¹:F))
    (fun j => Units.ne_zero _) (fun j => Units.ne_zero _)
  · intro j t
    rw [hu,hf]
  · intro j t
    rw [hl,hg]


theorem actual_root_coordinate_equiv {G : Type u} [Group G] (beta : MulAut G)
    (root : F → G) (hinj : Function.Injective root)
    (hadd : ∀ t s, root (t+s) = root t*root s)
    (hset : Set.range (fun t => beta (root t)) = Set.range root) :
    ∃ f : F ≃+ F, ∀ t, beta (root t) = root (f t) := by
  classical
  have hex : ∀ t, ∃ s, root s = beta (root t) := by
    intro t
    have hm : beta (root t) ∈ Set.range (fun t => beta (root t)) := ⟨t,rfl⟩
    rw [hset] at hm
    exact hm
  choose f hf using hex
  have hfadd : ∀ t s, f (t+s) = f t+f s := by
    intro t s
    apply hinj
    rw [hf,hadd,map_mul,← hf,← hf,← hadd]
  have hfi : Function.Injective f := by
    intro t s h
    apply hinj
    apply beta.injective
    rw [← hf,← hf,h]
  have hfs : Function.Surjective f := by
    intro s
    have hm : root s ∈ Set.range root := ⟨s,rfl⟩
    rw [← hset] at hm
    obtain ⟨t,ht⟩ := hm
    exact ⟨t,hinj ((hf t).trans ht)⟩
  refine ⟨{Equiv.ofBijective f ⟨hfi,hfs⟩ with map_add' := hfadd},?_⟩
  intro t
  exact (hf t).symm

/-- Actual root-pair stabilizer supply. The only structural hypotheses say
that beta preserves the two genuine root subgroups SETWISE. Additive root
coordinates and their field semilinearity are constructed, not assumed.
The scalar inner corrections still precede all full group targets. -/
theorem actual_root_stabilizing_SL2_scalar_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (beta : Fin (4*M) → MulAut SL(2,F)) (e : Fin (4*M) → ℕ)
    (hu : ∀ j, Set.range (fun t => beta j (upper t)) = Set.range upper)
    (hl : ∀ j, Set.range (fun t => beta j (lower t)) = Set.range lower) :
    PartIIScalarProductInput q (4*M) beta e := by
  classical
  choose f hf using fun j => actual_root_coordinate_equiv (beta j) upper upper_injective
    (Matrix.SpecialLinearGroup.transvection_add zero_ne_one) (hu j)
  choose g hg using fun j => actual_root_coordinate_equiv (beta j) lower lower_injective
    (Matrix.SpecialLinearGroup.transvection_add one_ne_zero) (hl j)
  exact actual_root_pair_SL2_scalar_product hq hM hF beta e f g hf hg
end NikolovSegal.PartIIA1RootSupply
