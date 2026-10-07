/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIPSL2RootNormalization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIPSL2RootNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bare projective root reconstruction and corrected scalar products. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIISL2RootAlignment
import Lean.Elab.Term
set_option autoImplicit false
set_option maxHeartbeats 2000000
/-! Actual PSL2 root-pair reconstruction. The accepted SL2 four-root/root-action
proofs are reused by their real imported private constants, resolved within their
original modules; the elaborated theorem body is checked by the kernel. -/
open Lean Elab Term in
elab "a1Kernel%" id:ident : term => do
  let env ← getEnv
  let moduleName := if id.getId == `exists_four_roots then "D5.S3.FiniteGroups.NikolovSegal.PartIISL2Scalar" else if (id.getId == `projective_corrected_power || id.getId == `projective_card_bound) then "D5.S3.FiniteGroups.NikolovSegal.PartIISL2Projective" else if id.getId == `root_pair_alignment then "D5.S3.FiniteGroups.NikolovSegal.PartIISL2RootAlignment" else "D5.S3.FiniteGroups.NikolovSegal.PartIISL2Semilinear"
  let suffix := ".NikolovSegal.PartIIA1RootSupply." ++ id.getId.toString
  let candidates := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some idx => env.header.moduleNames[idx.toNat]!.toString == moduleName
  match candidates with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique proved A1 kernel {id} from {moduleName} not found"
namespace NikolovSegal.PartIIA1RootSupply
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]
private def p : SL(2,F) →* PSL(2,F) := QuotientGroup.mk' (Subgroup.center _)
def projectiveUpper (t : F) : PSL(2,F) := p (upper t)
def projectiveLower (t : F) : PSL(2,F) := p (lower t)

private theorem projective_upper_injective : Function.Injective (projectiveUpper (F := F)) := by
  intro s t h
  have hm : (upper s)⁻¹*upper t ∈ Subgroup.center SL(2,F) := QuotientGroup.eq.mp h
  rw [show (upper s)⁻¹ = upper (-s) from Matrix.SpecialLinearGroup.transvection_inv _ s,
    show upper (-s)*upper t = upper (-s+t) from (Matrix.SpecialLinearGroup.transvection_add zero_ne_one _ _).symm] at hm
  have hh := (Matrix.SpecialLinearGroup.transvection_mem_center_iff zero_ne_one (-s+t)).mp hm
  linear_combination -hh
private theorem projective_lower_injective : Function.Injective (projectiveLower (F := F)) := by
  intro s t h
  have hm : (lower s)⁻¹*lower t ∈ Subgroup.center SL(2,F) := QuotientGroup.eq.mp h
  rw [show (lower s)⁻¹ = lower (-s) from Matrix.SpecialLinearGroup.transvection_inv _ s,
    show lower (-s)*lower t = lower (-s+t) from (Matrix.SpecialLinearGroup.transvection_add one_ne_zero _ _).symm] at hm
  have hh := (Matrix.SpecialLinearGroup.transvection_mem_center_iff one_ne_zero (-s+t)).mp hm
  linear_combination -hh

private theorem projective_conj (G H : SL(2,F)) :
    p (MulAut.conj G H) = MulAut.conj (p G) (p H) := by
  simp only [MulAut.conj_apply,map_mul,map_inv]

private theorem same_projective_zero (G H : SL(2,F)) (h : p G = p H)
    (i j : Fin 2) (hH : H i j = 0) : G i j = 0 := by
  obtain ⟨z,hz,hgh⟩ := (QuotientGroup.mk'_eq_mk' (Subgroup.center SL(2,F))).mp h
  obtain ⟨c,hc,hcz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hcn : c ≠ 0 := by intro hc0; simp [hc0] at hc
  have hh := congrArg (fun g : SL(2,F) => g.val) hgh
  change G.val*z.val = H.val at hh
  rw [← hcz] at hh
  have hij : (G.val*Matrix.scalar (Fin 2) c) i j = 0 := by rw [hh]; exact hH
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.scalar,Matrix.diagonal,Matrix.mul_apply,Fin.sum_univ_two] at hij
  all_goals exact hij.resolve_right hcn

private theorem projective_zero_diagonal (G : SL(2,F)) (t s : F) (ht : t ≠ 0)
    (h : MulAut.conj (p G) (projectiveUpper t) = projectiveLower s) : G 0 0 = 0 := by
  have hp : p (MulAut.conj G (upper t)) = p (lower s) := by
    rw [projective_conj]
    exact h
  have hz := same_projective_zero (MulAut.conj G (upper t)) (lower s) hp 0 1
    (by simp [lower,Matrix.SpecialLinearGroup.transvection_coe])
  change (G.val*(upper t).val*Matrix.adjugate G.val) 0 1 = 0 at hz
  rw [Matrix.adjugate_fin_two] at hz
  simp [upper,Matrix.SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_two] at hz
  have hh : (G 0 0)^2*t = 0 := by linear_combination hz
  exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_right ht)

private theorem projective_root_pair_semilinear [Finite F] (beta : MulAut PSL(2,F))
    (f g : F ≃+ F) (hu : ∀ t, beta (projectiveUpper t) = projectiveUpper (f t))
    (hl : ∀ t, beta (projectiveLower t) = projectiveLower (g t)) :
    ∃ a : Fˣ, ∃ phi : RingAut F, (∀ t, f t = (a:F)*phi t) ∧
      (∀ t, g t = (↑a⁻¹:F)*phi t) := by
  have hU : ∀ t, beta (p (upper t)) = p (upper (f t)) := hu
  have hL : ∀ t, beta (p (lower t)) = p (lower (g t)) := hl
  have hf1 : f 1 ≠ 0 := by intro h; exact one_ne_zero (f.injective (by simpa using h))
  have hc : ∀ W t, beta (MulAut.conj W (projectiveUpper t)) =
      MulAut.conj (beta W) (projectiveUpper (f t)) := by
    intro W t
    simp only [MulAut.conj_apply,map_mul,map_inv,hu]
  have hfg : ∀ x, x ≠ 0 → f x*g x⁻¹ = 1 := by
    intro x hx
    have hwu : ∀ t, MulAut.conj (p (a1Weyl x hx)) (projectiveUpper t) =
        projectiveLower (-(x⁻¹)^2*t) := by
      intro t
      change MulAut.conj (p (a1Weyl x hx)) (p (upper t)) = p (lower _)
      rw [← projective_conj,a1Weyl_upper]
    have hb : beta (p (a1Weyl x hx)) = p (upper (f x)*lower (-(g x⁻¹))*upper (f x)) := by
      rw [← a1Weyl_product]
      simp only [map_mul,hU,hL,map_neg]
    have hswap : MulAut.conj (p (upper (f x)*lower (-(g x⁻¹))*upper (f x))) (projectiveUpper (f 1)) =
        projectiveLower (g (-(x⁻¹)^2)) := by
      rw [← hb,← hc,hwu,mul_one,hl]
    have hz := projective_zero_diagonal (upper (f x)*lower (-(g x⁻¹))*upper (f x)) _ _ hf1 hswap
    change ((upper (f x)).val*(lower (-(g x⁻¹))).val*(upper (f x)).val) 0 0 = 0 at hz
    simp [upper,lower,Matrix.SpecialLinearGroup.transvection_coe,Matrix.mul_apply,
      Matrix.vecMul,dotProduct,Fin.sum_univ_two] at hz
    linear_combination -hz
  have hg1 : g 1 = (f 1)⁻¹ := by
    apply mul_left_cancel₀ hf1
    simpa only [inv_one,mul_inv_cancel₀ hf1] using hfg 1 one_ne_zero
  have hbw : beta (p (a1Weyl 1 one_ne_zero)) = p (a1Weyl (f 1) hf1) := by
    rw [← a1Weyl_product]
    simp only [map_mul,hU,hL,map_neg,inv_one,hg1]
    simpa only [map_mul] using congrArg p (a1Weyl_product _ hf1)
  have hg : ∀ t, g t = ((f 1)⁻¹)^2*f t := by
    intro t
    have hh := hc (p (a1Weyl 1 one_ne_zero)) t
    change beta (MulAut.conj (p (a1Weyl 1 one_ne_zero)) (p (upper t))) = MulAut.conj (beta (p (a1Weyl 1 one_ne_zero))) (p (upper (f t))) at hh
    rw [← projective_conj,a1Weyl_upper] at hh
    change beta (projectiveLower (-(1:F)⁻¹^2*t)) = _ at hh
    rw [inv_one,one_pow,neg_one_mul,hl,map_neg,hbw] at hh
    rw [← projective_conj,a1Weyl_upper] at hh
    change projectiveLower (-g t) = projectiveLower (-((f 1)⁻¹)^2*f t) at hh
    have h := projective_lower_injective hh
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

private theorem projective_root_pair_form [Finite F] (beta : MulAut PSL(2,F))
    (f g : F ≃+ F) (hu : ∀ t, beta (projectiveUpper t) = projectiveUpper (f t))
    (hl : ∀ t, beta (projectiveLower t) = projectiveLower (g t)) :
    ∃ a : Fˣ, ∃ phi : RingAut F, beta = projectiveAut (semilinearAut a phi) := by
  obtain ⟨a,phi,hf,hg⟩ := projective_root_pair_semilinear beta f g hu hl
  have hdU : ∀ t, semilinearAut a phi (upper t) = upper ((a:F)*phi t) := by
    intro t
    rw [semilinearAut,MulAut.mul_apply]
    exact (congrArg (diagonalAut a) ((a1Kernel% field_upper) phi t)).trans ((a1Kernel% diagonal_upper) a (phi t))
  have hdL : ∀ t, semilinearAut a phi (lower t) = lower ((↑a⁻¹:F)*phi t) := by
    intro t
    rw [semilinearAut,MulAut.mul_apply]
    exact (congrArg (diagonalAut a) ((a1Kernel% field_lower) phi t)).trans ((a1Kernel% diagonal_lower) a (phi t))
  refine ⟨a,phi,?_⟩
  apply MulEquiv.ext
  intro target
  obtain ⟨s,hs⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2,F)) target
  obtain ⟨x,y,z,v,hprod⟩ := (a1Kernel% exists_four_roots) s
  have hu' : ∀ t, beta (p (upper t)) = p (semilinearAut a phi (upper t)) := by
    intro t
    change beta (projectiveUpper t) = _
    rw [hu,hdU,hf]
    rfl
  have hl' : ∀ t, beta (p (lower t)) = p (semilinearAut a phi (lower t)) := by
    intro t
    change beta (projectiveLower t) = _
    rw [hl,hdL,hg]
    rfl
  rw [← hs]
  change beta (p s) = p (semilinearAut a phi s)
  rw [← hprod]
  simp only [map_mul,hu',hl']

/-- Actual PSL2 scalar supply for arbitrary root-pair-stabilizing automorphisms.
Their semilinear matrix form is PROVED from actual quotient root relations,
including the central scalar ambiguity; no lift/classification premise occurs. -/
theorem actual_root_stabilizing_PSL2_scalar_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (beta : Fin (4*M) → MulAut PSL(2,F)) (e : Fin (4*M) → ℕ)
    (hu : ∀ j, Set.range (fun t => beta j (projectiveUpper t)) = Set.range projectiveUpper)
    (hl : ∀ j, Set.range (fun t => beta j (projectiveLower t)) = Set.range projectiveLower) :
    PartIIScalarProductInput q (4*M) beta e := by
  classical
  choose f hf using fun j => actual_root_coordinate_equiv (beta j) projectiveUpper projective_upper_injective
    (by intro t s; simp only [projectiveUpper,upper,Matrix.SpecialLinearGroup.transvection_add,map_mul]) (hu j)
  choose g hg using fun j => actual_root_coordinate_equiv (beta j) projectiveLower projective_lower_injective
    (by intro t s; simp only [projectiveLower,lower,Matrix.SpecialLinearGroup.transvection_add,map_mul]) (hl j)
  choose a phi hbeta using fun j => projective_root_pair_form (beta j) (f j) (g j) (hf j) (hg j)
  have hb : beta = fun j => projectiveAut (semilinearAut (a j) (phi j)) := funext hbeta
  rw [hb]
  intro he
  obtain ⟨y,hy⟩ := actual_semilinear_SL2_scalar_product hq hM hF a phi e he
  refine ⟨fun j => p (y j),?_⟩
  intro target
  obtain ⟨s,hs⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2,F)) target
  change p s = target at hs
  obtain ⟨c,hc⟩ := hy s
  refine ⟨fun j => p (c j),?_⟩
  -- Exact arbitrary-auto quotient power commutation, imported from the previous module.
  have hpow : ∀ j n t, p (((semilinearAut (a j) (phi j)*MulAut.conj (y j)⁻¹)^n) t) =
      ((projectiveAut (semilinearAut (a j) (phi j))*MulAut.conj (p (y j))⁻¹)^n) (p t) := by
    intro j n t
    exact (a1Kernel% projective_corrected_power) (semilinearAut (a j) (phi j)) (y j) t n
  have hm : ∀ v : Fin (4*M) → SL(2,F), p (orderedProduct v) = orderedProduct (fun j => p (v j)) := by
    intro v
    simp only [orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def]
  have hv : ∀ j, p ((c j)⁻¹ * ((semilinearAut (a j) (phi j)*MulAut.conj (y j)⁻¹)^(q/e j)) (c j)) =
      (p (c j))⁻¹ * ((projectiveAut (semilinearAut (a j) (phi j))*MulAut.conj (p (y j))⁻¹)^(q/e j)) (p (c j)) := by
    intro j
    rw [map_mul,map_inv,hpow]
  have hh := congrArg p hc
  rw [hm,hs] at hh
  simpa only [hv,map_one,one_mul] using hh

private theorem projective_root_range_transport (A B : SL(2,F)) (root : F → SL(2,F)) :
    MulAut.conj (p A) '' Set.range (fun t => p (MulAut.conj B (root t))) =
      Set.range (fun t => p (MulAut.conj (A*B) (root t))) := by
  rw [← Set.range_comp']
  congr 1
  funext t
  simp only [MulAut.mul_apply,MulAut.conj_apply,map_mul,map_inv,mul_inv_rev]

private theorem projective_range_of_actual (A : SL(2,F)) (root : F → SL(2,F))
    (h : Set.range (fun t => MulAut.conj A (upper t)) = Set.range root) :
    Set.range (fun t => p (MulAut.conj A (upper t))) = Set.range (fun t => p (root t)) := by
  rw [Set.range_comp',h,← Set.range_comp']

/-- Actual PSL2 root-image consumer. Two genuine conjugates are inner-aligned;
projective root-pair normalization derives semilinearity and the actual full
scalar coverage follows. The independent root-Sylow theorem must supply A,B
for arbitrary beta; no automorphism-lift or coverage premise is introduced. -/
theorem actual_root_conjugate_PSL2_scalar_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (beta : Fin (4*M) → MulAut PSL(2,F)) (e : Fin (4*M) → ℕ)
    (A B : Fin (4*M) → SL(2,F))
    (hu : ∀ j, Set.range (fun t => beta j (projectiveUpper t)) =
      Set.range (fun t => p (MulAut.conj (A j) (upper t))))
    (hl : ∀ j, Set.range (fun t => beta j (projectiveLower t)) =
      Set.range (fun t => p (MulAut.conj (B j) (upper t)))) :
    PartIIScalarProductInput q (4*M) beta e := by
  classical
  have hne : ∀ j, Set.range (fun t => MulAut.conj (A j) (upper t)) ≠
      Set.range (fun t => MulAut.conj (B j) (upper t)) := by
    intro j h
    have hh := congrArg (fun V : Set SL(2,F) => p '' V) h
    rw [← Set.range_comp',← Set.range_comp',← hu,← hl] at hh
    have hm : beta j (projectiveUpper 1) ∈ Set.range (fun t => beta j (projectiveLower t)) := by
      rw [← hh]; exact ⟨1,rfl⟩
    obtain ⟨t,ht⟩ := hm
    have he := (beta j).injective ht
    have hz := same_projective_zero (upper 1) (lower t) he.symm 0 1
      (by simp [lower,Matrix.SpecialLinearGroup.transvection_coe])
    simp [upper,Matrix.SpecialLinearGroup.transvection_coe] at hz
  choose z hzu hzl using fun j => (a1Kernel% root_pair_alignment) (A j) (B j) (hne j)
  let gamma := fun j => MulAut.conj (p (z j))*beta j
  have hgu : ∀ j, Set.range (fun t => gamma j (projectiveUpper t)) = Set.range projectiveUpper := by
    intro j
    change Set.range (fun t => MulAut.conj (p (z j)) (beta j (projectiveUpper t))) = _
    rw [Set.range_comp',hu,projective_root_range_transport]
    exact projective_range_of_actual _ upper (hzu j)
  have hgl : ∀ j, Set.range (fun t => gamma j (projectiveLower t)) = Set.range projectiveLower := by
    intro j
    change Set.range (fun t => MulAut.conj (p (z j)) (beta j (projectiveLower t))) = _
    rw [Set.range_comp',hl,projective_root_range_transport]
    exact projective_range_of_actual _ lower (hzl j)
  intro he
  obtain ⟨y,hy⟩ := actual_root_stabilizing_PSL2_scalar_product hq hM hF gamma e hgu hgl he
  let x := fun j => y j*((beta j).symm (p (z j)))⁻¹
  have hx : ∀ j, beta j*MulAut.conj (x j)⁻¹ = gamma j*MulAut.conj (y j)⁻¹ := by
    intro j
    apply MulEquiv.ext
    intro s
    simp only [gamma,MulAut.mul_apply,MulAut.conj_apply]
    simp only [x,map_mul,map_inv,MulEquiv.apply_symm_apply]
    group
  refine ⟨x,?_⟩
  intro target
  obtain ⟨c,hc⟩ := hy target
  refine ⟨c,?_⟩
  simpa only [hx] using hc

end NikolovSegal.PartIIA1RootSupply
