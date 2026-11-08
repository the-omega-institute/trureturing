/- GID: D5/S3/Quantum/Algebra/FlatPairJointBlocks
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/FlatPairJointBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original-space circle and quaternionic frames for a flat skew pair. -/

module

public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Tactic

/-! Complete original-vector block specifications and metric orbit relations. -/

@[expose] public section

noncomputable section

open scoped InnerProductSpace
open Module.End

set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.Algebra.FlatPairJointBlocks

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- A complete orthonormal frame on the given space, grouped into circle and
quaternionic blocks. Parameters vary independently from block to block. Empty
index sets include the zero space. The quaternionic frame is ordered as
`q, J₁ q, J₂ q, J₁ J₂ q`. -/
def HasFlatPairJointBlocks (A D : F →ₗ[ℝ] F) : Prop :=
  ∃ (c h : ℕ)
    (b : OrthonormalBasis ((Fin c × Fin 2) ⊕ (Fin h × Fin 4)) ℝ F)
    (a d : Fin c → ℝ) (lam t : Fin h → ℝ),
    (∀ i, a i ^ 2 + d i ^ 2 = 1 ∧
      A (b (.inl (i, 0))) = a i • b (.inl (i, 1)) ∧
      A (b (.inl (i, 1))) = -(a i) • b (.inl (i, 0)) ∧
      D (b (.inl (i, 0))) = d i • b (.inl (i, 1)) ∧
      D (b (.inl (i, 1))) = -(d i) • b (.inl (i, 0))) ∧
    (∀ i, 0 < lam i ∧ lam i < 1 ∧ -1 < t i ∧ t i < 1 ∧
      A (b (.inr (i, 0))) = Real.sqrt (lam i) • b (.inr (i, 1)) ∧
      A (b (.inr (i, 1))) = -Real.sqrt (lam i) • b (.inr (i, 0)) ∧
      A (b (.inr (i, 2))) = Real.sqrt (lam i) • b (.inr (i, 3)) ∧
      A (b (.inr (i, 3))) = -Real.sqrt (lam i) • b (.inr (i, 2)) ∧
      D (b (.inr (i, 0))) = Real.sqrt (1 - lam i) •
        (t i • b (.inr (i, 1)) + Real.sqrt (1 - t i ^ 2) • b (.inr (i, 2))) ∧
      D (b (.inr (i, 1))) = Real.sqrt (1 - lam i) •
        (-(t i) • b (.inr (i, 0)) - Real.sqrt (1 - t i ^ 2) • b (.inr (i, 3))) ∧
      D (b (.inr (i, 2))) = Real.sqrt (1 - lam i) •
        (t i • b (.inr (i, 3)) - Real.sqrt (1 - t i ^ 2) • b (.inr (i, 0))) ∧
      D (b (.inr (i, 3))) = Real.sqrt (1 - lam i) •
        (-(t i) • b (.inr (i, 2)) + Real.sqrt (1 - t i ^ 2) • b (.inr (i, 1))))

private theorem flat_pair_joint_fiber_relations [Nontrivial F] (A D : F →ₗ[ℝ] F)
    (hA : ∀ x y, ⟪A x, y⟫_ℝ = -⟪x, A y⟫_ℝ)
    (hD : ∀ x y, ⟪D x, y⟫_ℝ = -⟪x, D y⟫_ℝ)
    (hflat : -(A * A) - D * D = 1) :
    (    let P := -(A * A)
    let S := (- (1 / 2 : ℝ)) • (A * D + D * A)
    P.IsSymmetric ∧ S.IsSymmetric ∧ Commute P S ∧
    Nonempty (DirectSum.Decomposition (fun m : Eigenvalues P × Eigenvalues S =>
      eigenspace P m.1 ⊓ eigenspace S m.2)) ∧
    (∀ r s : ℝ, ∀ x ∈ eigenspace P r ⊓ eigenspace S s,
      A x ∈ eigenspace P r ⊓ eigenspace S s ∧
      D x ∈ eigenspace P r ⊓ eigenspace S s) ∧
    (∀ r s : ℝ, ∀ x ∈ eigenspace P r ⊓ eigenspace S s,
      A (A x) = -r • x ∧ D (D x) = -(1 - r) • x ∧
      A (D x) + D (A x) = (-2 * s) • x ∧
      ⟪A x, A x⟫_ℝ = r * ⟪x, x⟫_ℝ ∧
      ⟪D x, D x⟫_ℝ = (1 - r) * ⟪x, x⟫_ℝ ∧
      ⟪A x, D x⟫_ℝ = s * ⟪x, x⟫_ℝ ∧
      (⟪x, x⟫_ℝ = 1 → 0 ≤ r ∧ r ≤ 1 ∧ s ^ 2 ≤ r * (1 - r)))) ∧
    (    ∃ r s : ℝ, ∃ q : F,
      q ∈ eigenspace (-(A*A)) r ⊓ eigenspace ((-(1/2:ℝ)) • (A*D+D*A)) s ∧
      ⟪q,q⟫_ℝ=1) := by
  have data :
      let P := -(A * A)
      let S := (- (1 / 2 : ℝ)) • (A * D + D * A)
      P.IsSymmetric ∧ S.IsSymmetric ∧ Commute P S ∧
      Nonempty (DirectSum.Decomposition (fun m : Eigenvalues P × Eigenvalues S =>
        eigenspace P m.1 ⊓ eigenspace S m.2)) ∧
      (∀ r s : ℝ, ∀ x ∈ eigenspace P r ⊓ eigenspace S s,
        A x ∈ eigenspace P r ⊓ eigenspace S s ∧
        D x ∈ eigenspace P r ⊓ eigenspace S s) ∧
      (∀ r s : ℝ, ∀ x ∈ eigenspace P r ⊓ eigenspace S s,
        A (A x) = -r • x ∧ D (D x) = -(1 - r) • x ∧
        A (D x) + D (A x) = (-2 * s) • x ∧
        ⟪A x, A x⟫_ℝ = r * ⟪x, x⟫_ℝ ∧
        ⟪D x, D x⟫_ℝ = (1 - r) * ⟪x, x⟫_ℝ ∧
        ⟪A x, D x⟫_ℝ = s * ⟪x, x⟫_ℝ ∧
        (⟪x, x⟫_ℝ = 1 → 0 ≤ r ∧ r ≤ 1 ∧ s ^ 2 ≤ r * (1 - r))) := by
    dsimp only
    let P := -(A * A)
    let S := (- (1 / 2 : ℝ)) • (A * D + D * A)
    have hP : P.IsSymmetric := by
      intro x y
      simp only [P, LinearMap.neg_apply, Module.End.mul_apply, inner_neg_left,
        inner_neg_right, hA, neg_neg]
    have hS : S.IsSymmetric := by
      intro x y
      simp only [S, LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply,
        real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
        hA, hD, neg_neg]
      ring
    have hP' : P = 1 + D * D := by
      dsimp [P]
      exact sub_eq_iff_eq_add.mp hflat
    have hPA : Commute P A := by dsimp [P, Commute, SemiconjBy]; noncomm_ring
    have hPD : Commute P D := by rw [hP']; dsimp [Commute, SemiconjBy]; noncomm_ring
    have hAAD : A * A * D = D * (A * A) := by
      have h := hPD.eq
      simpa only [P, neg_mul, mul_neg, neg_inj] using h
    have hDDA : D * D * A = A * (D * D) := by
      have h := hPA.eq
      rw [hP'] at h
      simp only [add_mul, mul_add, one_mul, mul_one] at h
      exact add_left_cancel h
    have hSA : Commute S A := by
      dsimp [S, Commute, SemiconjBy]
      rw [smul_mul_assoc, mul_smul_comm]
      congr 1
      calc
        (A * D + D * A) * A = A * D * A + D * (A * A) := by noncomm_ring
        _ = A * D * A + A * A * D := by rw [hAAD]
        _ = A * (A * D + D * A) := by noncomm_ring
    have hSD : Commute S D := by
      dsimp [S, Commute, SemiconjBy]
      rw [smul_mul_assoc, mul_smul_comm]
      congr 1
      calc
        (A * D + D * A) * D = A * (D * D) + D * A * D := by noncomm_ring
        _ = D * D * A + D * A * D := by rw [hDDA]
        _ = D * (A * D + D * A) := by noncomm_ring
    have hPS : Commute P S := by
      dsimp [S]
      exact (hPA.mul_right hPD).add_right (hPD.mul_right hPA) |>.smul_right _
    refine ⟨hP, hS, hPS, ⟨Commute.isSymmetric_directSumDecomposition hP hS hPS⟩, ?_, ?_⟩
    · intro r s x hx
      simp only [Submodule.mem_inf, mem_eigenspace_iff] at hx ⊢
      have move (T : F →ₗ[ℝ] F) (hPT : Commute P T) (hST : Commute S T) :
          P (T x) = r • T x ∧ S (T x) = s • T x := by
        constructor
        · rw [← Module.End.mul_apply, hPT.eq, Module.End.mul_apply, hx.1, map_smul]
        · rw [← Module.End.mul_apply, hST.eq, Module.End.mul_apply, hx.2, map_smul]
      exact ⟨move A hPA hSA, move D hPD hSD⟩
    · intro r s x hx
      rcases hx with ⟨hpx, hsx⟩
      replace hpx := mem_eigenspace_iff.mp hpx
      replace hsx := mem_eigenspace_iff.mp hsx
      change -(A (A x)) = r • x at hpx
      change (- (1 / 2 : ℝ)) • (A (D x) + D (A x)) = s • x at hsx
      have hAA : A (A x) = -r • x := by
        simpa only [neg_smul] using neg_eq_iff_eq_neg.mp hpx
      have hf := DFunLike.congr_fun hflat x
      change -(A (A x)) - D (D x) = x at hf
      have hDD : D (D x) = -(1 - r) • x := by
        rw [hAA] at hf
        have hh : D (D x) = -(-r • x) - x :=
          eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp hf).symm)
        rw [hh]
        module
      have hmix : A (D x) + D (A x) = (-2 * s) • x := by
        have hh := congrArg (fun y : F => (-2 : ℝ) • y) hsx
        norm_num [smul_smul] at hh
        simpa only [neg_mul, neg_smul] using hh
      have hna : ⟪A x, A x⟫_ℝ = r * ⟪x, x⟫_ℝ := by
        rw [hA, hAA, real_inner_smul_right]
        ring
      have hnd : ⟪D x, D x⟫_ℝ = (1 - r) * ⟪x, x⟫_ℝ := by
        rw [hD, hDD, real_inner_smul_right]
        ring
      have hcross : ⟪A x, D x⟫_ℝ = s * ⟪x, x⟫_ℝ := by
        have hm := congrArg (fun y : F => ⟪x, y⟫_ℝ) hmix
        simp only [inner_add_right, real_inner_smul_right] at hm
        have h₁ := hA x (D x)
        have h₂ := hD x (A x)
        rw [real_inner_comm (A x) (D x)] at h₂
        linarith
      refine ⟨hAA, hDD, hmix, hna, hnd, hcross, ?_⟩
      intro hn
      have hposA : 0 ≤ ⟪A x, A x⟫_ℝ := real_inner_self_nonneg
      have hposD : 0 ≤ ⟪D x, D x⟫_ℝ := real_inner_self_nonneg
      have hcs := real_inner_mul_inner_self_le (A x) (D x)
      simp only [hna, hnd, hcross, hn, mul_one] at hposA hposD hcs
      constructor
      · nlinarith
      constructor <;> nlinarith
  refine ⟨data,?_⟩

  classical
  obtain ⟨hP,hS,hPS,⟨dec⟩,hinv,hrel⟩ := data
  let P := -(A*A)
  let S := (-(1/2:ℝ)) • (A*D+D*A)
  let V := fun m : Eigenvalues P × Eigenvalues S => eigenspace P m.1 ⊓ eigenspace S m.2
  letI : DirectSum.Decomposition V := dec
  have htop : iSup V = ⊤ := (DirectSum.Decomposition.isInternal V).submodule_iSup_eq_top
  have hex : ∃ m, V m ≠ ⊥ := by
    by_contra! hh
    have hb : iSup V = ⊥ := iSup_eq_bot.mpr hh
    have hz : (⊤ : Submodule ℝ F) = ⊥ := htop.symm.trans hb
    exact top_ne_bot hz
  obtain ⟨m,hm⟩ := hex
  letI : Nontrivial (V m) := Submodule.nontrivial_iff_ne_bot.mpr hm
  obtain ⟨q,hq⟩ := exists_norm_eq (V m) (show (0:ℝ) ≤ 1 by norm_num)
  refine ⟨m.1,m.2,q,q.property,?_⟩
  change ⟪q,q⟫_ℝ=1
  rw [real_inner_self_eq_norm_sq,hq,one_pow]


omit [FiniteDimensional ℝ F] in
private theorem circle_orbit_span_data :
    (∀ (J : F →ₗ[ℝ] F)
    (hJ : ∀ x y, ⟪J x, y⟫_ℝ = -⟪x, J y⟫_ℝ)
    (hJ2 : ∀ x, J (J x) = -x) (q : F) (hq : ⟪q, q⟫_ℝ = 1),
    Orthonormal ℝ ![q, J q] ∧
    J q = (![q, J q] : Fin 2 → F) 1 ∧ J (J q) = -q ∧
    ∀ x ∈ Submodule.span ℝ (Set.range (![q, J q] : Fin 2 → F)),
      J x ∈ Submodule.span ℝ (Set.range (![q, J q] : Fin 2 → F))) ∧
    ((∀ (A D : F →ₗ[ℝ] F) (r s : ℝ)
    (hA : ∀ x y, ⟪A x, y⟫_ℝ = -⟪x, A y⟫_ℝ)
    (hD : ∀ x y, ⟪D x, y⟫_ℝ = -⟪x, D y⟫_ℝ)
    (hAA : ∀ x, A (A x) = -r • x)
    (hDD : ∀ x, D (D x) = -(1-r) • x)
    (hAD : ∀ x, A (D x) + D (A x) = (-2*s) • x)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : s^2 = r*(1-r)),
    ∃ (a d : ℝ) (J : F →ₗ[ℝ] F),
      a^2+d^2=1 ∧ (∀ x y, ⟪J x,y⟫_ℝ = -⟪x,J y⟫_ℝ) ∧
      (∀ x, J (J x) = -x) ∧ A = a • J ∧ D = d • J) ∧
    (∀ (A D : F →ₗ[ℝ] F) (a d : ℝ) (v : Fin 2 → F)
    (hv : Orthonormal ℝ v) (had : a^2+d^2=1)
    (ha0 : A (v 0)=a • v 1) (ha1 : A (v 1)= -a • v 0)
    (hd0 : D (v 0)=d • v 1) (hd1 : D (v 1)= -d • v 0),
    ∃ (U : Submodule ℝ F) (hAU : ∀ x ∈ U,A x ∈ U) (hDU : ∀ x ∈ U,D x ∈ U),
      U ≠ ⊥ ∧ HasFlatPairJointBlocks (A.restrict hAU) (D.restrict hDU))) := by
  constructor
  · intro J hJ hJ2 q hq
    have hcross : ⟪q, J q⟫_ℝ = 0 := by
      have h := hJ q q
      rw [real_inner_comm q (J q)] at h
      linarith
    have hnorm : ⟪J q, J q⟫_ℝ = 1 := by
      rw [hJ, hJ2, inner_neg_right, neg_neg, hq]
    refine ⟨?_, rfl, hJ2 q, ?_⟩
    · rw [orthonormal_iff_ite]
      intro i j
      fin_cases i <;> fin_cases j
      · exact hq
      · exact hcross
      · exact (real_inner_comm q (J q)).trans hcross
      · exact hnorm
    · have hqmem : q ∈ Submodule.span ℝ (Set.range (![q, J q] : Fin 2 → F)) :=
        Submodule.subset_span ⟨0, rfl⟩
      have hJmem : J q ∈ Submodule.span ℝ (Set.range (![q, J q] : Fin 2 → F)) :=
        Submodule.subset_span ⟨1, rfl⟩
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        fin_cases i
        · exact hJmem
        · change J (J q) ∈ _
          rw [hJ2]
          exact Submodule.neg_mem _ hqmem
      | zero => simp
      | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
      | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih
  · constructor
    · intro A D r s hA hD hAA hDD hAD hr hr1 hs
      have hnA (x : F) : ⟪A x,A x⟫_ℝ = r*⟪x,x⟫_ℝ := by
        rw [hA,hAA,real_inner_smul_right]; ring
      have hnD (x : F) : ⟪D x,D x⟫_ℝ = (1-r)*⟪x,x⟫_ℝ := by
        rw [hD,hDD,real_inner_smul_right]; ring
      have hnAD (x : F) : ⟪A x,D x⟫_ℝ = s*⟪x,x⟫_ℝ := by
        have hh := congrArg (fun y : F => ⟪x,y⟫_ℝ) (hAD x)
        simp only [inner_add_right,real_inner_smul_right] at hh
        have h1 := hA x (D x)
        have h2 := hD x (A x)
        rw [real_inner_comm (A x) (D x)] at h2
        linarith
      by_cases hz : r=0
      · have hAz : A=0 := by
          ext x
          apply (inner_self_eq_zero (𝕜 := ℝ)).mp
          rw [hnA,hz,zero_mul]
        refine ⟨0,1,D,by norm_num,hD,?_,?_,by simp⟩
        · intro x; simpa [hz] using hDD x
        · simp [hAz]
      have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
      let a := Real.sqrt r
      let d := s/a
      let J := a⁻¹ • A
      have ha : 0 < a := Real.sqrt_pos.2 hp
      have ha2 : a^2=r := Real.sq_sqrt hr
      have hd2 : d^2=1-r := by
        dsimp [d]; rw [div_pow,ha2,hs]; field_simp <;> ring
      have hJ : ∀ x y, ⟪J x,y⟫_ℝ = -⟪x,J y⟫_ℝ := by
        intro x y
        simp only [J,LinearMap.smul_apply,real_inner_smul_left,real_inner_smul_right,hA]
        ring
      have hJ2 : ∀ x, J (J x) = -x := by
        intro x
        simp only [J,LinearMap.smul_apply,map_smul,hAA,smul_smul]
        have hc : a⁻¹*(a⁻¹*(-r)) = -1 := by field_simp; nlinarith
        rw [hc,neg_one_smul]
      have hAc : A=a • J := by dsimp [J]; rw [smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
      have hDc : D=d • J := by
        ext x
        apply sub_eq_zero.mp
        apply (inner_self_eq_zero (𝕜 := ℝ)).mp
        change ⟪D x - (s/a) • (a⁻¹ • A x), D x - (s/a) • (a⁻¹ • A x)⟫_ℝ = 0
        rw [inner_sub_left,inner_sub_right,inner_sub_right]
        simp only [real_inner_smul_left,real_inner_smul_right]
        rw [real_inner_comm (A x) (D x),hnAD,hnA,hnD]
        have he : (1-r)-2*(s/a)*a⁻¹*s+((s/a)*a⁻¹)^2*r = 0 := by
          field_simp [ha.ne']
          rw [←ha2] at hs ⊢
          linear_combination -(a^2)*hs
        calc
          _ = ((1-r)-2*(s/a)*a⁻¹*s+((s/a)*a⁻¹)^2*r) * ⟪x,x⟫_ℝ := by ring
          _ = 0 := by rw [he,zero_mul]
      exact ⟨a,d,J,by nlinarith,hJ,hJ2,hAc,hDc⟩
    · intro A D a d v hv had ha0 ha1 hd0 hd1
      classical
      let U := Submodule.span ℝ (Set.range v)
      have memv (k : Fin 2) : v k ∈ U := Submodule.subset_span ⟨k,rfl⟩
      have inv (T : F →ₗ[ℝ] F) (ht : ∀ k,T (v k) ∈ U) : ∀ x ∈ U,T x ∈ U := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx => obtain ⟨k,rfl⟩ := hx; exact ht k
        | zero => simp
        | add x y hx hy ihx ihy => simpa only [map_add] using U.add_mem ihx ihy
        | smul r x hx ih => simpa only [map_smul] using U.smul_mem r ih
      have hAU : ∀ x ∈ U,A x ∈ U := inv A (by
        intro k; fin_cases k
        · change A (v 0) ∈ U; rw [ha0];exact U.smul_mem _ (memv 1)
        · change A (v 1) ∈ U; rw [ha1];exact U.smul_mem _ (memv 0))
      have hDU : ∀ x ∈ U,D x ∈ U := inv D (by
        intro k; fin_cases k
        · change D (v 0) ∈ U; rw [hd0];exact U.smul_mem _ (memv 1)
        · change D (v 1) ∈ U; rw [hd1];exact U.smul_mem _ (memv 0))
      have hU : U ≠ ⊥ := by
        intro hz
        have hm := memv 0
        rw [hz,Submodule.mem_bot] at hm
        exact hv.ne_zero 0 hm
      let b0 : OrthonormalBasis (Fin 2) ℝ U :=
        (Module.Basis.span hv.linearIndependent).toOrthonormalBasis (by
          rw [orthonormal_iff_ite]; intro i j; simpa only [Submodule.coe_inner, Module.Basis.coe_span_apply] using (orthonormal_iff_ite.mp hv i j))
      have hb0 (k : Fin 2) : (b0 k : F)=v k := by
        have hh := congrFun (Module.Basis.coe_toOrthonormalBasis (Module.Basis.span hv.linearIndependent)
          (by rw [orthonormal_iff_ite]; intro i j; simpa only [Submodule.coe_inner, Module.Basis.coe_span_apply] using (orthonormal_iff_ite.mp hv i j))) k
        simpa only [Module.Basis.span_apply] using congrArg ((↑) : U → F) hh
      let e : Fin 2 ≃ ((Fin 1 × Fin 2) ⊕ (Fin 0 × Fin 4)) :=
        { toFun := fun k => .inl (0,k)
          invFun := fun i => match i with | .inl (_,k) => k | .inr (i,_) => Fin.elim0 i
          left_inv := fun _ => rfl
          right_inv := by
            rintro (⟨i,k⟩|⟨i,k⟩)
            · have hz : i=0 := Subsingleton.elim _ _; subst i; rfl
            · exact Fin.elim0 i }
      let b := b0.reindex e
      have hb (k : Fin 2) : (b (.inl (0,k)) : F)=v k := by
        simp [b,OrthonormalBasis.reindex_apply,e,hb0]
      refine ⟨U,hAU,hDU,hU,1,0,b,fun _=>a,fun _=>d,Fin.elim0,Fin.elim0,?_,?_⟩
      · intro i; have hi : i=0 := Subsingleton.elim _ _; subst i
        refine ⟨had,?_,?_,?_,?_⟩ <;> apply Subtype.ext
        · simpa only [LinearMap.restrict_apply,Submodule.coe_smul,hb] using ha0
        · simpa only [LinearMap.restrict_apply,Submodule.coe_smul,hb] using ha1
        · simpa only [LinearMap.restrict_apply,Submodule.coe_smul,hb] using hd0
        · simpa only [LinearMap.restrict_apply,Submodule.coe_smul,hb] using hd1
      · intro i; exact Fin.elim0 i

omit [FiniteDimensional ℝ F] in
private theorem quaternion_orbit_span_data :
    (∀ (I J : F →ₗ[ℝ] F)
    (hI : ∀ x y, ⟪I x, y⟫_ℝ = -⟪x, I y⟫_ℝ)
    (hJ : ∀ x y, ⟪J x, y⟫_ℝ = -⟪x, J y⟫_ℝ)
    (hI2 : ∀ x, I (I x) = -x) (hJ2 : ∀ x, J (J x) = -x)
    (hIJ : ∀ x, I (J x) = -J (I x)) (q : F) (hq : ⟪q, q⟫_ℝ = 1),
    let v : Fin 4 → F := ![q, I q, J q, I (J q)]
    Orthonormal ℝ v ∧
    (∀ k, I (v k) = (![v 1, -v 0, v 3, -v 2] : Fin 4 → F) k) ∧
    (∀ k, J (v k) = (![v 2, -v 3, -v 0, v 1] : Fin 4 → F) k) ∧
    (∀ x ∈ Submodule.span ℝ (Set.range v), I x ∈ Submodule.span ℝ (Set.range v)) ∧
    (∀ x ∈ Submodule.span ℝ (Set.range v), J x ∈ Submodule.span ℝ (Set.range v))) ∧
    ((∀ (A D : F →ₗ[ℝ] F) (r s : ℝ)
    (hA : ∀ x y, ⟪A x, y⟫_ℝ = -⟪x, A y⟫_ℝ)
    (hD : ∀ x y, ⟪D x, y⟫_ℝ = -⟪x, D y⟫_ℝ)
    (hAA : A * A = -r • (1 : F →ₗ[ℝ] F))
    (hDD : D * D = -(1-r) • (1 : F →ₗ[ℝ] F))
    (hAD : A * D + D * A = (-2*s) • (1 : F →ₗ[ℝ] F))
    (hr : 0 < r) (hr1 : r < 1) (hs : s^2 < r*(1-r)),
    let a := Real.sqrt r
    let d := Real.sqrt (1-r)
    let t := s/(a*d)
    let I := a⁻¹ • A
    let J := (Real.sqrt (1-t^2))⁻¹ • (d⁻¹ • D - t • I);
    -1 < t ∧ t < 1 ∧
    (∀ x y, ⟪I x, y⟫_ℝ = -⟪x, I y⟫_ℝ) ∧
    (∀ x y, ⟪J x, y⟫_ℝ = -⟪x, J y⟫_ℝ) ∧
    I*I = -1 ∧ J*J = -1 ∧ I*J = -(J*I) ∧
    A = a • I ∧ D = d • (t • I + Real.sqrt (1-t^2) • J)) ∧
    (∀ (A D : F →ₗ[ℝ] F) (r t : ℝ) (v : Fin 4 → F)
    (hv : Orthonormal ℝ v) (hr : 0<r) (hr1 : r<1) (ht : -1<t) (ht1 : t<1)
    (ha0 : A (v 0)=Real.sqrt r • v 1) (ha1 : A (v 1)= -Real.sqrt r • v 0)
    (ha2 : A (v 2)=Real.sqrt r • v 3) (ha3 : A (v 3)= -Real.sqrt r • v 2)
    (hd0 : D (v 0)=Real.sqrt (1-r) • (t • v 1+Real.sqrt (1-t^2) • v 2))
    (hd1 : D (v 1)=Real.sqrt (1-r) • (-t • v 0-Real.sqrt (1-t^2) • v 3))
    (hd2 : D (v 2)=Real.sqrt (1-r) • (t • v 3-Real.sqrt (1-t^2) • v 0))
    (hd3 : D (v 3)=Real.sqrt (1-r) • (-t • v 2+Real.sqrt (1-t^2) • v 1)),
    ∃ (U : Submodule ℝ F) (hAU : ∀ x ∈ U,A x ∈ U) (hDU : ∀ x ∈ U,D x ∈ U),
      U ≠ ⊥ ∧ HasFlatPairJointBlocks (A.restrict hAU) (D.restrict hDU))) := by
  constructor
  · intro I J hI hJ hI2 hJ2 hIJ q hq
    dsimp only
    have hJI (x : F) : J (I x) = -I (J x) := by
      rw [hIJ, neg_neg]
    have isoI (x y : F) : ⟪I x, I y⟫_ℝ = ⟪x, y⟫_ℝ := by
      rw [hI, hI2, inner_neg_right, neg_neg]
    have isoJ (x y : F) : ⟪J x, J y⟫_ℝ = ⟪x, y⟫_ℝ := by
      rw [hJ, hJ2, inner_neg_right, neg_neg]
    have skewIJ (x y : F) : ⟪I (J x), y⟫_ℝ = -⟪x, I (J y)⟫_ℝ := by
      rw [hI, hJ, neg_neg, hJI, inner_neg_right]
    have diag (T : F →ₗ[ℝ] F)
        (hT : ∀ x y, ⟪T x, y⟫_ℝ = -⟪x, T y⟫_ℝ) (x : F) :
        ⟪x, T x⟫_ℝ = 0 := by
      have hh := hT x x
      rw [real_inner_comm x (T x)] at hh
      linarith
    have diagIJ : ⟪q, I (J q)⟫_ℝ = 0 := by
      have hh := skewIJ q q
      rw [real_inner_comm q (I (J q))] at hh
      linarith
    have hcross : ⟪I q, J q⟫_ℝ = 0 := by rw [hI, diagIJ, neg_zero]
    have horth : Orthonormal ℝ (![q, I q, J q, I (J q)] : Fin 4 → F) := by
      rw [orthonormal_iff_ite]
      intro i j
      fin_cases i <;> fin_cases j
      · exact hq
      · exact diag I hI q
      · exact diag J hJ q
      · exact diagIJ
      · exact (real_inner_comm q (I q)).trans (diag I hI q)
      · exact (isoI q q).trans hq
      · exact hcross
      · exact (isoI q (J q)).trans (diag J hJ q)
      · exact (real_inner_comm q (J q)).trans (diag J hJ q)
      · exact (real_inner_comm (I q) (J q)).trans hcross
      · exact (isoJ q q).trans hq
      · exact diag I hI (J q)
      · exact (real_inner_comm q (I (J q))).trans diagIJ
      · exact (real_inner_comm (I q) (I (J q))).trans
          ((isoI q (J q)).trans (diag J hJ q))
      · exact (real_inner_comm (J q) (I (J q))).trans (diag I hI (J q))
      · exact (isoI (J q) (J q)).trans ((isoJ q q).trans hq)
    have tableI : ∀ k : Fin 4, I ((![q, I q, J q, I (J q)] : Fin 4 → F) k) =
        (![I q, -q, I (J q), -J q] : Fin 4 → F) k := by
      intro k; fin_cases k <;> simp [hI2]
    have tableJ : ∀ k : Fin 4, J ((![q, I q, J q, I (J q)] : Fin 4 → F) k) =
        (![J q, -I (J q), -q, I q] : Fin 4 → F) k := by
      intro k; fin_cases k <;> simp [hJ2, hJI, map_neg]
    have memv (k : Fin 4) :
        (![q, I q, J q, I (J q)] : Fin 4 → F) k ∈
          Submodule.span ℝ (Set.range (![q, I q, J q, I (J q)] : Fin 4 → F)) :=
      Submodule.subset_span ⟨k, rfl⟩
    have inv (T : F →ₗ[ℝ] F)
        (ht : ∀ k : Fin 4, T ((![q, I q, J q, I (J q)] : Fin 4 → F) k) ∈
          Submodule.span ℝ (Set.range (![q, I q, J q, I (J q)] : Fin 4 → F))) :
        ∀ x ∈ Submodule.span ℝ (Set.range (![q, I q, J q, I (J q)] : Fin 4 → F)),
          T x ∈ Submodule.span ℝ (Set.range (![q, I q, J q, I (J q)] : Fin 4 → F)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨k, rfl⟩ := hx; exact ht k
      | zero => simp
      | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
      | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih
    refine ⟨horth, ?_, ?_, inv I ?_, inv J ?_⟩
    · simpa using tableI
    · simpa using tableJ
    · intro k; rw [tableI]; fin_cases k
      · exact memv 1
      · exact Submodule.neg_mem _ (memv 0)
      · exact memv 3
      · exact Submodule.neg_mem _ (memv 2)
    · intro k; rw [tableJ]; fin_cases k
      · exact memv 2
      · exact Submodule.neg_mem _ (memv 3)
      · exact Submodule.neg_mem _ (memv 0)
      · exact memv 1
  · constructor
    · intro A D r s hA hD hAA hDD hAD hr hr1 hs
      dsimp only
      let a := Real.sqrt r
      let d := Real.sqrt (1-r)
      let t := s/(a*d)
      let I := a⁻¹ • A
      let K := d⁻¹ • D
      let u := Real.sqrt (1-t^2)
      let J := u⁻¹ • (K-t • I)
      have ha : 0 < a := Real.sqrt_pos.2 hr
      have hd : 0 < d := Real.sqrt_pos.2 (by linarith)
      have ha2 : a^2 = r := Real.sq_sqrt hr.le
      have hd2 : d^2 = 1-r := Real.sq_sqrt (by linarith)
      have had : 0 < a*d := mul_pos ha hd
      have ht2 : t^2 < 1 := by
        dsimp [t]
        rw [div_pow, div_lt_one (sq_pos_of_pos had)]
        nlinarith
      have ht : -1 < t ∧ t < 1 := by constructor <;> nlinarith [sq_nonneg (t+1),sq_nonneg (t-1)]
      have hu : 0 < u := Real.sqrt_pos.2 (by linarith)
      have hu2 : u^2 = 1-t^2 := Real.sq_sqrt (by linarith)
      have hI : ∀ x y, ⟪I x,y⟫_ℝ = -⟪x,I y⟫_ℝ := by
        intro x y; simp only [I,LinearMap.smul_apply,real_inner_smul_left,real_inner_smul_right,hA]; ring
      have hK : ∀ x y, ⟪K x,y⟫_ℝ = -⟪x,K y⟫_ℝ := by
        intro x y; simp only [K,LinearMap.smul_apply,real_inner_smul_left,real_inner_smul_right,hD]; ring
      have hJ : ∀ x y, ⟪J x,y⟫_ℝ = -⟪x,J y⟫_ℝ := by
        intro x y
        simp only [J,LinearMap.smul_apply,LinearMap.sub_apply,real_inner_smul_left,
          real_inner_smul_right,inner_sub_left,inner_sub_right,hI,hK]
        ring
      have hI2 : I*I = -1 := by
        simp only [I,smul_mul_smul_comm,hAA,smul_smul]
        have hc : a⁻¹*a⁻¹*(-r) = -1 := by field_simp; nlinarith
        rw [hc,neg_one_smul]
      have hK2 : K*K = -1 := by
        simp only [K,smul_mul_smul_comm,hDD,smul_smul]
        have hc : d⁻¹*d⁻¹*(-(1-r)) = -1 := by field_simp; nlinarith
        rw [hc,neg_one_smul]
      have hIK : I*K + K*I = (-2*t) • (1 : F →ₗ[ℝ] F) := by
        dsimp [I,K]
        simp only [smul_mul_smul_comm]
        rw [mul_comm d⁻¹ a⁻¹,←smul_add,hAD,smul_smul]
        congr 1
        dsimp [t]; field_simp <;> ring
      have hJ2 : J*J = -1 := by
        have he : (K-t • I)*(K-t • I) = (-(1-t^2)) • (1 : F →ₗ[ℝ] F) := by
          calc
            (K-t • I)*(K-t • I) = K*K - t • (I*K+K*I) + (t*t) • (I*I) := by
              simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,smul_smul,smul_add]
              module
            _ = _ := by rw [hK2,hI2,hIK]; module
        dsimp [J]
        rw [smul_mul_smul_comm,he,smul_smul]
        have hc : u⁻¹*u⁻¹*(-(1-t^2)) = -1 := by field_simp; nlinarith
        rw [hc,neg_one_smul]
      have hIJ : I*J = -(J*I) := by
        apply eq_neg_iff_add_eq_zero.mpr
        calc
          I*J+J*I = u⁻¹ • (I*K+K*I-(2*t) • (I*I)) := by
            dsimp [J]
            simp only [mul_smul_comm,smul_mul_assoc,mul_sub,sub_mul,smul_add,smul_sub]
            module
          _ = 0 := by rw [hIK,hI2]; module
      refine ⟨ht.1,ht.2,hI,hJ,hI2,hJ2,hIJ,?_,?_⟩
      · change A = a • I
        dsimp [I]; rw [smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
      · change D = d • (t • I + u • J)
        dsimp [J]
        simp only [smul_smul,mul_inv_cancel₀ hu.ne',one_smul,add_sub_cancel]
        dsimp [K]
        rw [smul_smul,mul_inv_cancel₀ hd.ne',one_smul]
    · intro A D r t v hv hr hr1 ht ht1 ha0 ha1 ha2 ha3 hd0 hd1 hd2 hd3
      classical
      let U := Submodule.span ℝ (Set.range v)
      have memv (k : Fin 4) : v k ∈ U := Submodule.subset_span ⟨k,rfl⟩
      have inv (T : F →ₗ[ℝ] F) (ht : ∀ k,T (v k) ∈ U) : ∀ x ∈ U,T x ∈ U := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx => obtain ⟨k,rfl⟩ := hx; exact ht k
        | zero => simp
        | add x y hx hy ihx ihy => simpa only [map_add] using U.add_mem ihx ihy
        | smul r x hx ih => simpa only [map_smul] using U.smul_mem r ih
      have hAU : ∀ x ∈ U,A x ∈ U := inv A (by
        intro k; fin_cases k
        · change A (v 0) ∈ U; rw [ha0];exact U.smul_mem _ (memv 1)
        · change A (v 1) ∈ U; rw [ha1];exact U.smul_mem _ (memv 0)
        · change A (v 2) ∈ U; rw [ha2];exact U.smul_mem _ (memv 3)
        · change A (v 3) ∈ U; rw [ha3];exact U.smul_mem _ (memv 2))
      have hDU : ∀ x ∈ U,D x ∈ U := inv D (by
        intro k; fin_cases k
        · change D (v 0) ∈ U; rw [hd0];exact U.smul_mem _ (U.add_mem (U.smul_mem _ (memv 1)) (U.smul_mem _ (memv 2)))
        · change D (v 1) ∈ U; rw [hd1];exact U.smul_mem _ (U.sub_mem (U.smul_mem _ (memv 0)) (U.smul_mem _ (memv 3)))
        · change D (v 2) ∈ U; rw [hd2];exact U.smul_mem _ (U.sub_mem (U.smul_mem _ (memv 3)) (U.smul_mem _ (memv 0)))
        · change D (v 3) ∈ U; rw [hd3];exact U.smul_mem _ (U.add_mem (U.smul_mem _ (memv 2)) (U.smul_mem _ (memv 1))))
      have hU : U ≠ ⊥ := by
        intro hz
        have hm := memv 0
        rw [hz,Submodule.mem_bot] at hm
        exact hv.ne_zero 0 hm
      let b0 : OrthonormalBasis (Fin 4) ℝ U :=
        (Module.Basis.span hv.linearIndependent).toOrthonormalBasis (by
          rw [orthonormal_iff_ite]; intro i j; simpa only [Submodule.coe_inner, Module.Basis.coe_span_apply] using (orthonormal_iff_ite.mp hv i j))
      have hb0 (k : Fin 4) : (b0 k : F)=v k := by
        have hh := congrFun (Module.Basis.coe_toOrthonormalBasis (Module.Basis.span hv.linearIndependent)
          (by rw [orthonormal_iff_ite]; intro i j; simpa only [Submodule.coe_inner, Module.Basis.coe_span_apply] using (orthonormal_iff_ite.mp hv i j))) k
        simpa only [Module.Basis.span_apply] using congrArg ((↑) : U → F) hh
      let e : Fin 4 ≃ ((Fin 0 × Fin 2) ⊕ (Fin 1 × Fin 4)) :=
        { toFun := fun k => .inr (0,k)
          invFun := fun i => match i with | .inr (_,k) => k | .inl (i,_) => Fin.elim0 i
          left_inv := fun _ => rfl
          right_inv := by
            rintro (⟨i,k⟩|⟨i,k⟩)
            · exact Fin.elim0 i
            · have hz : i=0 := Subsingleton.elim _ _; subst i; rfl }
      let b := b0.reindex e
      have hb (k : Fin 4) : (b (.inr (0,k)) : F)=v k := by
        simp [b,OrthonormalBasis.reindex_apply,e,hb0]
      refine ⟨U,hAU,hDU,hU,0,1,b,Fin.elim0,Fin.elim0,fun _=>r,fun _=>t,?_,?_⟩
      · intro i; exact Fin.elim0 i
      · intro i; have hi : i=0 := Subsingleton.elim _ _; subst i
        refine ⟨hr,hr1,ht,ht1,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply Subtype.ext
        · simpa only [LinearMap.restrict_apply,Submodule.coe_smul,Submodule.coe_add,Submodule.coe_sub,hb] using ha0
        · simpa only [LinearMap.restrict_apply,Submodule.coe_smul,Submodule.coe_add,Submodule.coe_sub,hb] using ha1
        · simpa only [LinearMap.restrict_apply,Submodule.coe_smul,Submodule.coe_add,Submodule.coe_sub,hb] using ha2
        · simpa only [LinearMap.restrict_apply,Submodule.coe_smul,Submodule.coe_add,Submodule.coe_sub,hb] using ha3
        · simpa only [LinearMap.restrict_apply,Submodule.coe_smul,Submodule.coe_add,Submodule.coe_sub,hb] using hd0
        · simpa only [LinearMap.restrict_apply,Submodule.coe_smul,Submodule.coe_add,Submodule.coe_sub,hb] using hd1
        · simpa only [LinearMap.restrict_apply,Submodule.coe_smul,Submodule.coe_add,Submodule.coe_sub,hb] using hd2
        · simpa only [LinearMap.restrict_apply,Submodule.coe_smul,Submodule.coe_add,Submodule.coe_sub,hb] using hd3

private theorem flat_pair_complement_descent_data (A D : F →ₗ[ℝ] F)
    (hA : ∀ x y, ⟪A x, y⟫_ℝ = -⟪x, A y⟫_ℝ)
    (hD : ∀ x y, ⟪D x, y⟫_ℝ = -⟪x, D y⟫_ℝ)
    (hflat : -(A * A) - D * D = 1)
    (V : Submodule ℝ F) (hV : V ≠ ⊥)
    (hAV : ∀ x ∈ V, A x ∈ V) (hDV : ∀ x ∈ V, D x ∈ V) :
    ∃ (hAc : ∀ x ∈ Vᗮ, A x ∈ Vᗮ) (hDc : ∀ x ∈ Vᗮ, D x ∈ Vᗮ),
      (∀ x y : Vᗮ, ⟪A.restrict hAc x, y⟫_ℝ = -⟪x, A.restrict hAc y⟫_ℝ) ∧
      (∀ x y : Vᗮ, ⟪D.restrict hDc x, y⟫_ℝ = -⟪x, D.restrict hDc y⟫_ℝ) ∧
      -(A.restrict hAc * A.restrict hAc) - D.restrict hDc * D.restrict hDc = 1 ∧
      Module.finrank ℝ Vᗮ < Module.finrank ℝ F ∧
      (HasFlatPairJointBlocks (A.restrict hAV) (D.restrict hDV) →
       HasFlatPairJointBlocks (A.restrict hAc) (D.restrict hDc) →
       HasFlatPairJointBlocks A D) := by
  have comp (T : F →ₗ[ℝ] F)
      (hT : ∀ x y, ⟪T x, y⟫_ℝ = -⟪x, T y⟫_ℝ)
      (hTV : ∀ x ∈ V, T x ∈ V) : ∀ x ∈ Vᗮ, T x ∈ Vᗮ := by
    intro x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro y hy
    have hz := hx (T y) (hTV y hy)
    have hh := hT y x
    linarith
  let hAc := comp A hA hAV
  let hDc := comp D hD hDV
  refine ⟨hAc, hDc, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y; exact hA x y
  · intro x y; exact hD x y
  · ext x
    exact DFunLike.congr_fun hflat (x : F)
  · have hpos : 0 < Module.finrank ℝ V :=
      Nat.pos_of_ne_zero (fun hz => hV (Submodule.finrank_eq_zero.mp hz))
    have hadd := V.finrank_add_finrank_orthogonal
    omega
  · intro hframeV hframeW
    classical
    rcases hframeV with ⟨c,h,b,a,d,r,t,hC,hQ⟩
    rcases hframeW with ⟨c',h',b',a',d',r',t',hC',hQ'⟩
    let eC : ((Fin c × Fin 2) ⊕ (Fin c' × Fin 2)) ≃ (Fin (c+c') × Fin 2) :=
      (Equiv.sumProdDistrib _ _ _).symm.trans (Equiv.prodCongr finSumFinEquiv (Equiv.refl _))
    let eH : ((Fin h × Fin 4) ⊕ (Fin h' × Fin 4)) ≃ (Fin (h+h') × Fin 4) :=
      (Equiv.sumProdDistrib _ _ _).symm.trans (Equiv.prodCongr finSumFinEquiv (Equiv.refl _))
    let e := (Equiv.sumSumSumComm (Fin c × Fin 2) (Fin h × Fin 4)
        (Fin c' × Fin 2) (Fin h' × Fin 4)).trans (Equiv.sumCongr eC eH)
    let B := ((b.prod b').map V.orthogonalDecomposition.symm).reindex e
    let aa : Fin (c+c') → ℝ := Sum.elim a a' ∘ finSumFinEquiv.symm
    let dd : Fin (c+c') → ℝ := Sum.elim d d' ∘ finSumFinEquiv.symm
    let rr : Fin (h+h') → ℝ := Sum.elim r r' ∘ finSumFinEquiv.symm
    let tt : Fin (h+h') → ℝ := Sum.elim t t' ∘ finSumFinEquiv.symm
    have bC (i : Fin c) (k : Fin 2) :
        B (.inl (finSumFinEquiv (.inl i),k)) = (b (.inl (i,k)) : F) := by
      simp [B,e,eC,eH,OrthonormalBasis.reindex_apply,Equiv.sumSumSumComm,
        Equiv.sumProdDistrib,OrthonormalBasis.prod_apply]
    have bC' (i : Fin c') (k : Fin 2) :
        B (.inl (finSumFinEquiv (.inr i),k)) = (b' (.inl (i,k)) : F) := by
      simp [B,e,eC,eH,OrthonormalBasis.reindex_apply,Equiv.sumSumSumComm,
        Equiv.sumProdDistrib,OrthonormalBasis.prod_apply]
    have bH (i : Fin h) (k : Fin 4) :
        B (.inr (finSumFinEquiv (.inl i),k)) = (b (.inr (i,k)) : F) := by
      simp [B,e,eC,eH,OrthonormalBasis.reindex_apply,Equiv.sumSumSumComm,
        Equiv.sumProdDistrib,OrthonormalBasis.prod_apply]
    have bH' (i : Fin h') (k : Fin 4) :
        B (.inr (finSumFinEquiv (.inr i),k)) = (b' (.inr (i,k)) : F) := by
      simp [B,e,eC,eH,OrthonormalBasis.reindex_apply,Equiv.sumSumSumComm,
        Equiv.sumProdDistrib,OrthonormalBasis.prod_apply]
    refine ⟨c+c',h+h',B,aa,dd,rr,tt,?_,?_⟩
    · intro j
      obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective j
      cases i with
      | inl i =>
        have hc := hC i
        simp only [Subtype.ext_iff,LinearMap.restrict_apply,Submodule.coe_smul] at hc
        simpa only [aa,dd,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl,bC] using hc
      | inr i =>
        have hc := hC' i
        simp only [Subtype.ext_iff,LinearMap.restrict_apply,Submodule.coe_smul] at hc
        simpa only [aa,dd,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr,bC'] using hc
    · intro j
      obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective j
      cases i with
      | inl i =>
        have hq := hQ i
        simp only [Subtype.ext_iff,LinearMap.restrict_apply,Submodule.coe_smul,
          Submodule.coe_add,Submodule.coe_sub] at hq
        simpa only [rr,tt,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl,bH] using hq
      | inr i =>
        have hq := hQ' i
        simp only [Subtype.ext_iff,LinearMap.restrict_apply,Submodule.coe_smul,
          Submodule.coe_add,Submodule.coe_sub] at hq
        simpa only [rr,tt,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr,bH'] using hq


set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
/-- Complete original-space classification and converse for a finite real flat skew pair. -/
theorem flat_pair_joint_blocks_iff (A D : F →ₗ[ℝ] F) :
    HasFlatPairJointBlocks A D ↔
    (∀ x y, ⟪A x,y⟫_ℝ = -⟪x,A y⟫_ℝ) ∧
    (∀ x y, ⟪D x,y⟫_ℝ = -⟪x,D y⟫_ℝ) ∧ -(A*A)-D*D=1 := by
  constructor
  · intro hf
    classical
    rcases hf with ⟨c,h,b,a,d,r,t,hC,hQ⟩
    have onA : ∀ i j, ⟪A (b i),b j⟫_ℝ = -⟪b i,A (b j)⟫_ℝ := by
      rintro (⟨i,k⟩|⟨i,k⟩) (⟨j,l⟩|⟨j,l⟩)
      · rcases hC i with ⟨hi,hi0,hi1,_,_⟩
        rcases hC j with ⟨hj,hj0,hj1,_,_⟩
        by_cases hij : i=j
        · subst j; fin_cases k <;> fin_cases l <;>
            simp [hi0,hi1,real_inner_smul_left,real_inner_smul_right,b.inner_eq_ite]
        · fin_cases k <;> fin_cases l <;>
            simp [hi0,hi1,hj0,hj1,real_inner_smul_left,real_inner_smul_right,b.inner_eq_ite,hij]
      · rcases hC i with ⟨_,hi0,hi1,_,_⟩
        rcases hQ j with ⟨_,_,_,_,hj0,hj1,hj2,hj3,_,_,_,_⟩
        fin_cases k <;> fin_cases l <;>
          simp [hi0,hi1,hj0,hj1,hj2,hj3,real_inner_smul_left,real_inner_smul_right,b.inner_eq_ite]
      · rcases hQ i with ⟨_,_,_,_,hi0,hi1,hi2,hi3,_,_,_,_⟩
        rcases hC j with ⟨_,hj0,hj1,_,_⟩
        fin_cases k <;> fin_cases l <;>
          simp [hi0,hi1,hi2,hi3,hj0,hj1,real_inner_smul_left,real_inner_smul_right,b.inner_eq_ite]
      · rcases hQ i with ⟨_,_,_,_,hi0,hi1,hi2,hi3,_,_,_,_⟩
        rcases hQ j with ⟨_,_,_,_,hj0,hj1,hj2,hj3,_,_,_,_⟩
        by_cases hij : i=j
        · subst j; fin_cases k <;> fin_cases l <;>
            simp [hi0,hi1,hi2,hi3,real_inner_smul_left,real_inner_smul_right,b.inner_eq_ite]
        · fin_cases k <;> fin_cases l <;>
            simp [hi0,hi1,hi2,hi3,hj0,hj1,hj2,hj3,real_inner_smul_left,real_inner_smul_right,b.inner_eq_ite,hij]
    have onD : ∀ i j, ⟪D (b i),b j⟫_ℝ = -⟪b i,D (b j)⟫_ℝ := by
      rintro (⟨i,k⟩|⟨i,k⟩) (⟨j,l⟩|⟨j,l⟩)
      · rcases hC i with ⟨_,_,_,hi0,hi1⟩
        rcases hC j with ⟨_,_,_,hj0,hj1⟩
        by_cases hij : i=j
        · subst j; fin_cases k <;> fin_cases l <;>
            simp [hi0,hi1,real_inner_smul_left,real_inner_smul_right,b.inner_eq_ite]
        · fin_cases k <;> fin_cases l <;>
            simp [hi0,hi1,hj0,hj1,real_inner_smul_left,real_inner_smul_right,b.inner_eq_ite,hij]
      · rcases hC i with ⟨_,_,_,hi0,hi1⟩
        rcases hQ j with ⟨_,_,_,_,_,_,_,_,hj0,hj1,hj2,hj3⟩
        fin_cases k <;> fin_cases l <;>
          simp [hi0,hi1,hj0,hj1,hj2,hj3,real_inner_smul_left,real_inner_smul_right,
            inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,b.inner_eq_ite]
      · rcases hQ i with ⟨_,_,_,_,_,_,_,_,hi0,hi1,hi2,hi3⟩
        rcases hC j with ⟨_,_,_,hj0,hj1⟩
        fin_cases k <;> fin_cases l <;>
          simp [hi0,hi1,hi2,hi3,hj0,hj1,real_inner_smul_left,real_inner_smul_right,
            inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,b.inner_eq_ite]
      · rcases hQ i with ⟨_,_,_,_,_,_,_,_,hi0,hi1,hi2,hi3⟩
        rcases hQ j with ⟨_,_,_,_,_,_,_,_,hj0,hj1,hj2,hj3⟩
        by_cases hij : i=j
        · subst j; fin_cases k <;> fin_cases l <;>
            simp [hi0,hi1,hi2,hi3,real_inner_smul_left,real_inner_smul_right,
              inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,b.inner_eq_ite] <;> ring
        · fin_cases k <;> fin_cases l <;>
            simp [hi0,hi1,hi2,hi3,hj0,hj1,hj2,hj3,real_inner_smul_left,real_inner_smul_right,
              inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,b.inner_eq_ite,hij]
    have extend (T : F →ₗ[ℝ] F)
        (ht : ∀ i j, ⟪T (b i),b j⟫_ℝ = -⟪b i,T (b j)⟫_ℝ) :
        ∀ x y, ⟪T x,y⟫_ℝ = -⟪x,T y⟫_ℝ := by
      intro x y
      conv_lhs => rw [←b.sum_repr x,←b.sum_repr y]
      conv_rhs => rw [←b.sum_repr x,←b.sum_repr y]
      simp only [map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,
        real_inner_smul_right,ht,Finset.sum_neg_distrib]
      simp only [mul_neg,Finset.sum_neg_distrib]
    refine ⟨extend A onA,extend D onD,?_⟩
    apply b.toBasis.ext
    rintro (⟨i,k⟩|⟨i,k⟩)
    · rcases hC i with ⟨hi,ha0,ha1,hd0,hd1⟩
      fin_cases k
      · change -(A (A (b (.inl (i,0)))))-D (D (b (.inl (i,0))))=b (.inl (i,0))
        simp only [ha0,ha1,hd0,hd1,map_smul,smul_smul]
        match_scalars <;> nlinarith
      · change -(A (A (b (.inl (i,1)))))-D (D (b (.inl (i,1))))=b (.inl (i,1))
        simp only [ha0,ha1,hd0,hd1,map_smul,smul_smul]
        match_scalars <;> nlinarith
    · rcases hQ i with ⟨hr,hr1,ht,ht1,ha0,ha1,ha2,ha3,hd0,hd1,hd2,hd3⟩
      have hs := Real.sq_sqrt (show 0 ≤ 1-t i^2 by nlinarith)
      have ha := Real.sq_sqrt hr.le
      have hd := Real.sq_sqrt (show 0 ≤ 1-r i by linarith)
      have hall : Real.sqrt (r i)^2 + Real.sqrt (1-r i)^2 *
          (t i^2 + Real.sqrt (1-t i^2)^2) = 1 := by rw [ha,hd,hs]; ring
      fin_cases k
      · change -(A (A (b (.inr (i,0)))))-D (D (b (.inr (i,0))))=b (.inr (i,0))
        simp only [ha0,ha1,ha2,ha3,hd0,hd1,hd2,hd3,map_smul,map_add,map_sub,smul_smul]
        match_scalars <;> nlinarith
      · change -(A (A (b (.inr (i,1)))))-D (D (b (.inr (i,1))))=b (.inr (i,1))
        simp only [ha0,ha1,ha2,ha3,hd0,hd1,hd2,hd3,map_smul,map_add,map_sub,smul_smul]
        match_scalars <;> nlinarith
      · change -(A (A (b (.inr (i,2)))))-D (D (b (.inr (i,2))))=b (.inr (i,2))
        simp only [ha0,ha1,ha2,ha3,hd0,hd1,hd2,hd3,map_smul,map_add,map_sub,smul_smul]
        match_scalars <;> nlinarith
      · change -(A (A (b (.inr (i,3)))))-D (D (b (.inr (i,3))))=b (.inr (i,3))
        simp only [ha0,ha1,ha2,ha3,hd0,hd1,hd2,hd3,map_smul,map_add,map_sub,smul_smul]
        match_scalars <;> nlinarith
  · rintro ⟨hA,hD,hflat⟩
    have go : ∀ n (E : Type _) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E], Module.finrank ℝ E = n → ∀ (A D : E →ₗ[ℝ] E),
        (∀ x y, ⟪A x,y⟫_ℝ = -⟪x,A y⟫_ℝ) →
        (∀ x y, ⟪D x,y⟫_ℝ = -⟪x,D y⟫_ℝ) → -(A*A)-D*D=1 →
        HasFlatPairJointBlocks A D := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro E _ _ _ hdim A D hA hD hflat
        classical
        by_cases hz : n=0
        · letI : Subsingleton E := Module.finrank_zero_iff.mp (hdim.trans hz)
          let v : ((Fin 0 × Fin 2) ⊕ (Fin 0 × Fin 4)) → E := fun _=>0
          let b := OrthonormalBasis.mk (Orthonormal.of_isEmpty (𝕜 := ℝ) v) (by
            intro x hx
            rw [Subsingleton.elim x 0]
            exact Submodule.zero_mem _)
          exact ⟨0,0,b,Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,
            by intro i; exact Fin.elim0 i,by intro i; exact Fin.elim0 i⟩
        letI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
        obtain ⟨data,r,s,q,hqmem,hq⟩ := flat_pair_joint_fiber_relations A D hA hD hflat
        obtain ⟨_,_,_,_,hinv,hrel⟩ := data
        obtain ⟨_,_,_,_,_,_,hbounds⟩ := hrel r s q hqmem
        obtain ⟨hr,hr1,hs⟩ := hbounds hq
        let V := eigenspace (-(A*A)) r ⊓ eigenspace ((-(1/2:ℝ)) • (A*D+D*A)) s
        let hAV : ∀ x ∈ V,A x ∈ V := fun x hx => (hinv r s x hx).1
        let hDV : ∀ x ∈ V,D x ∈ V := fun x hx => (hinv r s x hx).2
        let AV := A.restrict hAV
        let DV := D.restrict hDV
        let qV : V := ⟨q,hqmem⟩
        have hqV : ⟪qV,qV⟫_ℝ=1 := hq
        have skewA : ∀ x y : V, ⟪AV x,y⟫_ℝ = -⟪x,AV y⟫_ℝ := fun x y => hA x y
        have skewD : ∀ x y : V, ⟪DV x,y⟫_ℝ = -⟪x,DV y⟫_ℝ := fun x y => hD x y
        have sqA (x : V) : AV (AV x) = -r • x := by
          apply Subtype.ext; exact (hrel r s x x.property).1
        have sqD (x : V) : DV (DV x) = -(1-r) • x := by
          apply Subtype.ext; exact (hrel r s x x.property).2.1
        have mix (x : V) : AV (DV x)+DV (AV x)=(-2*s) • x := by
          apply Subtype.ext; exact (hrel r s x x.property).2.2.1
        have single : ∃ (U : Submodule ℝ E) (hAU : ∀ x ∈ U,A x ∈ U)
            (hDU : ∀ x ∈ U,D x ∈ U),
            U ≠ ⊥ ∧ HasFlatPairJointBlocks (A.restrict hAU) (D.restrict hDU) := by
          by_cases heq : s^2=r*(1-r)
          · obtain ⟨a,d,J,had,hJ,hJ2,hAj,hDj⟩ :=
              (circle_orbit_span_data (F := V)).2.1 AV DV r s skewA skewD sqA sqD mix hr hr1 heq
            have geo := (circle_orbit_span_data (F := V)).1 J hJ hJ2 qV hqV
            let vv : Fin 2 → V := ![qV,J qV]
            let v : Fin 2 → E := fun k => (vv k : E)
            have hon : Orthonormal ℝ v := geo.1.comp_linearIsometry V.subtypeₗᵢ
            apply (circle_orbit_span_data (F := E)).2.2 A D a d v hon had
            · change (AV qV : E)=a • (J qV : E)
              exact congrArg ((↑) : V → E) (show AV qV = a • J qV by rw [hAj]; rfl)
            · change (AV (J qV) : E)= -a • (qV : E)
              exact congrArg ((↑) : V → E) (show AV (J qV) = -a • qV by simp [hAj,hJ2,smul_neg,neg_smul])
            · change (DV qV : E)=d • (J qV : E)
              exact congrArg ((↑) : V → E) (show DV qV = d • J qV by rw [hDj]; rfl)
            · change (DV (J qV) : E)= -d • (qV : E)
              exact congrArg ((↑) : V → E) (show DV (J qV) = -d • qV by simp [hDj,hJ2,smul_neg,neg_smul])
          · have hslt : s^2 < r*(1-r) := lt_of_le_of_ne hs heq
            have hrp : 0<r := by nlinarith [sq_nonneg s]
            have hrq : r<1 := by nlinarith [sq_nonneg s]
            have opA : AV*AV= -r • (1 : V →ₗ[ℝ] V) := LinearMap.ext sqA
            have opD : DV*DV= -(1-r) • (1 : V →ₗ[ℝ] V) := LinearMap.ext sqD
            have opM : AV*DV+DV*AV= (-2*s) • (1 : V →ₗ[ℝ] V) := LinearMap.ext mix
            let a := Real.sqrt r
            let d := Real.sqrt (1-r)
            let t := s/(a*d)
            let I := a⁻¹ • AV
            let J := (Real.sqrt (1-t^2))⁻¹ • (d⁻¹ • DV-t • I)
            have normdata := (quaternion_orbit_span_data (F := V)).2.1
              AV DV r s skewA skewD opA opD opM hrp hrq hslt
            change -1<t ∧ t<1 ∧ _ at normdata
            obtain ⟨ht,ht1,hI,hJ,hI2,hJ2,hIJ,hAj,hDj⟩ := normdata
            change AV = a • I at hAj
            change DV = d • (t • I + Real.sqrt (1-t^2) • J) at hDj
            have sqI (x : V) : I (I x)= -x := DFunLike.congr_fun hI2 x
            have sqJ (x : V) : J (J x)= -x := DFunLike.congr_fun hJ2 x
            have ant (x : V) : I (J x)= -J (I x) := DFunLike.congr_fun hIJ x
            have geo := (quaternion_orbit_span_data (F := V)).1 I J hI hJ sqI sqJ ant qV hqV
            let vv : Fin 4 → V := ![qV,I qV,J qV,I (J qV)]
            let v : Fin 4 → E := fun k => (vv k : E)
            obtain ⟨hon,tableI,tableJ,_,_⟩ := geo
            have horth : Orthonormal ℝ v := hon.comp_linearIsometry V.subtypeₗᵢ
            have actA (k : Fin 4) : AV (vv k)=a • (![vv 1,-vv 0,vv 3,-vv 2] : Fin 4 → V) k := by
              rw [hAj]; exact congrArg (fun x : V => a • x) (tableI k)
            have actD (k : Fin 4) : DV (vv k)=d •
                (t • (![vv 1,-vv 0,vv 3,-vv 2] : Fin 4 → V) k+
                 Real.sqrt (1-t^2) • (![vv 2,-vv 3,-vv 0,vv 1] : Fin 4 → V) k) := by
              have hIv : I (vv k) = (![vv 1,-vv 0,vv 3,-vv 2] : Fin 4 → V) k := tableI k
              have hJv : J (vv k) = (![vv 2,-vv 3,-vv 0,vv 1] : Fin 4 → V) k := tableJ k
              rw [hDj]
              change d • (t • I (vv k)+Real.sqrt (1-t^2) • J (vv k)) = _
              rw [hIv,hJv]
            apply (quaternion_orbit_span_data (F := E)).2.2 A D r t v horth hrp hrq ht ht1
            · simpa [v,vv,a,d,smul_neg,neg_smul,sub_eq_add_neg] using congrArg ((↑) : V → E) (actA 0)
            · simpa [v,vv,a,d,smul_neg,neg_smul,sub_eq_add_neg] using congrArg ((↑) : V → E) (actA 1)
            · simpa [v,vv,a,d,smul_neg,neg_smul,sub_eq_add_neg] using congrArg ((↑) : V → E) (actA 2)
            · simpa [v,vv,a,d,smul_neg,neg_smul,sub_eq_add_neg] using congrArg ((↑) : V → E) (actA 3)
            · simpa [v,vv,a,d,smul_neg,neg_smul,sub_eq_add_neg] using congrArg ((↑) : V → E) (actD 0)
            · simpa [v,vv,a,d,smul_neg,neg_smul,sub_eq_add_neg] using congrArg ((↑) : V → E) (actD 1)
            · simpa [v,vv,a,d,smul_neg,neg_smul,sub_eq_add_neg] using congrArg ((↑) : V → E) (actD 2)
            · simpa [v,vv,a,d,smul_neg,neg_smul,sub_eq_add_neg] using congrArg ((↑) : V → E) (actD 3)
        obtain ⟨U,hAU,hDU,hU,hframe⟩ := single
        obtain ⟨hAc,hDc,hAs,hDs,hf,hd,join⟩ :=
          flat_pair_complement_descent_data A D hA hD hflat U hU hAU hDU
        apply join hframe
        exact ih (Module.finrank ℝ Uᗮ) (by omega) Uᗮ rfl (A.restrict hAc) (D.restrict hDc) hAs hDs hf
    exact go (Module.finrank ℝ F) F rfl A D hA hD hflat

end D5.S3.Quantum.Algebra.FlatPairJointBlocks
