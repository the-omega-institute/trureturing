/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeBracketIdentities
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeBracketIdentities
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Explicit relative primitives for the skew and Jacobi defects. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBracket
import D5.S3.VertexAlgebra.StateField.SkewSymmetry
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionVertexAlgebra
import Mathlib.Data.Nat.Choose.Sum

/-! The translation primitive for the relative skew defect and its Jacobi consequence. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open ActualLeechOrbifoldCriticalMatter (matter hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge)
open LatticeQuartetContraction (chargeProject)
open RelativeCohomology (GradedCycles GradedCohomology)
open private assocY_modes term_truncation
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes
open private ghost_square ward Q_T E_b E_T degree_b degree_T momentum_b momentum_T
  degree_mode momentum_mode from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCurrent
open private native_mem native_degree native_closed boundary_of_native
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBracket

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup
local notation "Cycles" => GradedCycles planeFrame planeBasis
local notation "Coh" => GradedCohomology planeFrame planeBasis

local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _
local instance (p : Charge hyperbolicPlane) (g : ℤ) : AddCommGroup (Cycles p g) :=
  Submodule.addCommGroup _

private theorem mode_closed (n : ℤ) {u v : ComplexState}
    (qu : Q u = 0) (qv : Q v = 0) : Q (originalMode n u v) = 0 := by
  rw [actualQ_mode_superderivation, qu, qv]
  simp only [map_zero, LinearMap.zero_apply, add_zero]

private theorem energy_mode
    (n : ℤ) {u v : ComplexState} (bu : b0 u = 0) (bv : b0 v = 0)
    (qu : Q u = 0) (qv : Q v = 0) :
    E (originalMode n u v) = -((n + 1 : ℤ) : ℂ) • originalMode n u v := by
  rw [← ward 0, mode_closed n qu qv, actual_b0_mode, bu, bv]
  simp only [map_zero, LinearMap.zero_apply, zero_add, add_zero]
  have hBu : Q (B u) = T u := by
    simpa only [qu, map_zero, add_zero] using ward (-1) u
  rw [actualQ_mode_superderivation, hBu, qv, map_zero, add_zero, translation_mode,
    show n + 1 - 1 = n by omega]

private theorem mode_tail (u v : ComplexState) :
    ∃ N₀ : ℕ, ∀ k ≥ N₀, originalMode (k : ℤ) u v = 0 := by
  obtain ⟨M, hM⟩ := term_truncation (reassoc u) (reassoc v)
  refine ⟨M.toNat, fun k hk => reassoc.injective ?_⟩
  rw [reassoc_originalMode, assocY_modes]
  exact (finsum_eq_zero_of_forall_eq_zero (hM _ (by omega))).trans reassoc.map_zero.symm

private def skewCoefficient (k : ℕ) : ℂ :=
  -((-1 : ℂ) ^ (k + 1)) / ((k + 1).factorial : ℂ)

def skewCorrection (u v : ComplexState) (k : ℕ) : ComplexState :=
  skewCoefficient k • (T ^ (k + 1)) (originalMode (k : ℤ) v u)

/-- Actual odd/odd super-skew at mode -1, with the j=0 term on the left. -/
abbrev OddProductSkewLaw : Prop :=
  ∀ (u v : ComplexState), Degree 1 u → Degree 1 v →
    originalMode (-1) u v + originalMode (-1) v u = ∑ᶠ k : ℕ, skewCorrection u v k

section NativeSkew

open ActualLeechOrbifoldMatter (Orbifold leechUnit leechPosDef)
open ActualLeechHyperbolic (leechData)
open TwistedGround.Orbifold
open StateField.BorcherdsPermutations (dividedTranslation)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open private assocY_tmul assocParity reassoc_parity orb_tail
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes
open private assocT reassoc_T
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCurrent
open private rightLift_tmul from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone
open private parity_square from D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBRSTDerivation

private abbrev PlaneGhost := LatticeMatterGhostCoupling.State hyperbolicPlane
local notation "orbY" => OriginalOrbifoldField.Y leechData leechUnit leechPosDef
local notation "orbT" => OriginalOrbifoldTranslation.T leechData leechUnit
local notation "planeY" => LatticeMatterGhostStateField.Y hyperbolicPlane
local notation "planeT" => LatticeMatterGhostStateField.translation hyperbolicPlane
local notation "par" => LatticeMatterGhostStateField.parity hyperbolicPlane
local notation "vac" => LatticeMatterGhostStateField.vacuum hyperbolicPlane

private theorem orb_skew (a b : Orbifold) (n : ℤ) :
    ((orbY a)[[n]]) b = ∑ᶠ i : ℕ,
      epsilon (n + i + 1) • dividedTranslation orbT i (((orbY b)[[n+i]]) a) := by
  have h := ((StateField.SkewSymmetry.skew_symmetry
    ActualLeechExtensionVertexAlgebra.leechVertexAlgebra a b).1 n).2
  have hT : ActualLeechExtensionVertexAlgebra.leechVertexAlgebra.translation = orbT := rfl
  rw [ActualLeechExtensionVertexAlgebra.stateField_eq, hT] at h
  simpa only [epsilon, dividedTranslation, LinearMap.smul_apply, smul_smul, div_eq_mul_inv] using h

private theorem plane_creation (x : PlaneGhost) (i : ℕ) :
    ((planeY x)[[-(i : ℤ)-1]]) vac = dividedTranslation planeT i x := by
  have hv := LatticeMatterGhostStateField.stateField_vacuum_creation hyperbolicPlane
  induction i with
  | zero => simpa [dividedTranslation] using hv.2.1 x
  | succ i ih =>
    have h := congrArg (fun f : Module.End ℂ PlaneGhost => f vac)
      (LatticeMatterGhostStateField.stateField_covariance hyperbolicPlane x (-(i : ℤ)-1))
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      hv.2.2.2, map_zero, sub_zero, ih, dividedTranslation, map_smul] at h
    have hn : ((i+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
    have hcast : (-((-(i : ℤ)-1 : ℤ) : ℂ)) = ((i+1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast] at h
    have hc := congrArg (fun w : PlaneGhost => (((i+1 : ℕ) : ℂ)⁻¹) • w) h
    simp only [smul_smul, inv_mul_cancel₀ hn, one_smul] at hc
    rw [dividedTranslation, LinearMap.smul_apply, Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
    simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one, pow_succ',
      Module.End.mul_apply, mul_comm, show -(i : ℤ)-1-1 = -(i.succ : ℤ)-1 by omega] using hc.symm

private theorem plane_skew (x y : PlaneGhost) (hx : par x = -x) (hy : par y = -y) (n : ℤ) :
    ((planeY x)[[n]]) y = ∑ᶠ j : ℕ,
      (-epsilon (n + j + 1)) • dividedTranslation planeT j (((planeY y)[[n+j]]) x) := by
  have hv := (LatticeMatterGhostStateField.stateField_vacuum_creation hyperbolicPlane).2
  have h := LatticeMatterGhostBorcherds.borcherds hyperbolicPlane y x vac (-1) 0 n
  have even : (2 : ℂ)⁻¹ • (y + par y) = 0 := by rw [hy, add_neg_cancel, smul_zero]
  have odd : (2 : ℂ)⁻¹ • (y - par y) = y := by rw [hy]; module
  have law := h.2.2.2.2
  simp only [LatticeMatterGhostSignedBorcherds.jacobiLeftTerm,
    LatticeMatterGhostSignedBorcherds.mu_D, even, odd, hx, map_zero, Pi.zero_apply,
    LinearMap.zero_apply, map_neg, Pi.neg_apply, LinearMap.neg_apply, zero_add,
    smul_neg, sub_neg_eq_add] at law
  have rhs : (∑ᶠ i : ℕ, (((-1 : ℂ)^i) * integerBinomial n i) •
      (((planeY y)[[-1+n-i]]) (((planeY x)[[(i : ℤ)]]) vac) +
        epsilon n • ((planeY x)[[n-i]]) (((planeY y)[[-1+i]]) vac))) =
      epsilon n • ((planeY x)[[n]]) y := by
    rw [finsum_eq_single _ 0]
    · simp [integerBinomial, hv.2.1 x 0 (by omega), hv.1 y]
    · intro i hi
      rw [hv.2.1 x i (by omega), hv.2.1 y (-1+(i : ℤ)) (by omega)]
      simp
  rw [rhs] at law
  have hs : epsilon n * epsilon n = 1 := by
    rw [epsilon, ← mul_zpow]
    norm_num
  have scaled := congrArg (fun w : PlaneGhost => epsilon n • w) law
  have leftFinite := h.1
  change Function.HasFiniteSupport (fun i : ℕ => integerBinomial (-1) i •
    ((planeY (((planeY y)[[n+i]]) x))[[-1+0-i]]) vac) at leftFinite
  rw [smul_finsum' _ leftFinite] at scaled
  simp only [smul_smul, hs, one_smul] at scaled
  rw [← scaled]
  apply finsum_congr
  intro i
  rw [show (-1 : ℤ) + 0 - (i : ℤ) = -(i : ℤ)-1 by omega, plane_creation]
  simp only [integerBinomial, Ring.choose_neg', Ring.multichoose_one, Units.smul_def]
  congr 1
  rw [epsilon, epsilon, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast]
  norm_num [mul_comm]

private theorem divided_assoc_translation (s : ℕ) (a : Orbifold) (x : PlaneGhost) :
    dividedTranslation assocT s (a ⊗ₜ[ℂ] x) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal s,
        dividedTranslation orbT ij.1 a ⊗ₜ[ℂ] dividedTranslation planeT ij.2 x := by
  let L : Module.End ℂ AssocState := (orbT).rTensor PlaneGhost
  let R : Module.End ℂ AssocState := rightLift planeT
  have comm : Commute L R := by
    apply TensorProduct.ext'
    intro b y
    simp only [L, R, Module.End.mul_apply, rightLift_tmul, LinearMap.rTensor_tmul]
  change ((s.factorial : ℂ)⁻¹) • ((L + R) ^ s) (a ⊗ₜ[ℂ] x) = _
  rw [comm.add_pow']
  simp only [LinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have ht := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have hfac : (s.choose ij.1 : ℂ) * (ij.1.factorial : ℂ) * (ij.2.factorial : ℂ) =
      (s.factorial : ℂ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show ij.1 ≤ s by omega)
    rw [show s - ij.1 = ij.2 by omega] at h
    exact_mod_cast h
  simp only [← Nat.cast_smul_eq_nsmul ℂ, LinearMap.smul_apply, Module.End.mul_apply,
    L, R, LinearMap.rTensor_pow, ← map_pow, rightLift_tmul, LinearMap.rTensor_tmul,
    dividedTranslation, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  congr 1
  have hs : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero s
  have hi : (ij.1.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero ij.1
  have hj : (ij.2.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero ij.2
  congr 1
  field_simp
  linear_combination hfac

private theorem finsum_by_total {V : Type*} [AddCommMonoid V] (f : ℕ × ℕ → V) (K : ℕ)
    (tail : ∀ i j : ℕ, K ≤ i + j → f (i,j) = 0) :
    (∑ᶠ ij, f ij) = ∑ s ∈ Finset.range K, ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal s, f ij := by
  let box := ((Finset.range K) ×ˢ (Finset.range K)).filter (fun ij => ij.1 + ij.2 < K)
  have hsub : Function.support f ⊆ (↑box : Set (ℕ × ℕ)) := by
    rintro ⟨i,j⟩ hij
    have h : i + j < K := lt_of_not_ge (fun h => hij (tail i j h))
    simp [box, Finset.mem_range, show i < K by omega, show j < K by omega, h]
  rw [finsum_eq_sum_of_support_subset f hsub]
  have hmap : ∀ ij ∈ box, ij.1 + ij.2 ∈ Finset.range K := by
    intro ij hij
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hij).2
  rw [← Finset.sum_fiberwise_of_maps_to hmap f]
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  ext ⟨i,j⟩
  have hk := Finset.mem_range.mp hs
  simp only [box, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.HasAntidiagonal.mem_antidiagonal]
  omega

private theorem assoc_tmul_skew (a b : Orbifold) (x y : PlaneGhost)
    (hx : par x = -x) (hy : par y = -y) :
    ((assocY (a ⊗ₜ[ℂ] x))[[-1]]) (b ⊗ₜ[ℂ] y) = ∑ᶠ s : ℕ,
      (-((-1 : ℂ) ^ s)) • dividedTranslation assocT s
        (((assocY (b ⊗ₜ[ℂ] y))[[((s : ℤ) - 1)]]) (a ⊗ₜ[ℂ] x)) := by
  classical
  let F : ℤ → Orbifold := fun p => ((orbY b)[[p]]) a
  let G : ℤ → PlaneGhost := fun q => ((planeY y)[[q]]) x
  obtain ⟨M, hM⟩ : ∃ M, ∀ p ≥ M, F p = 0 := orb_tail b a
  obtain ⟨N, hN⟩ : ∃ N, ∀ q ≥ N, G q = 0 :=
    LatticeMatterGhostStateField.stateField_truncation hyperbolicPlane y x
  let K := (M + N + 2).toNat
  let rev (s : ℕ) (p : ℤ) := F p ⊗ₜ[ℂ] G ((s : ℤ) - 1 - 1 - p)
  have revFinite (s : ℕ) : Function.HasFiniteSupport (rev s) := by
    refine (Finset.Icc ((s : ℤ) - 1 - N) (M - 1)).finite_toSet.subset ?_
    intro p hp
    have hpM : p < M := lt_of_not_ge fun h => hp (by simp [rev, hM p h])
    have hpN : (s : ℤ) - 1 - 1 - p < N := lt_of_not_ge fun h => hp (by simp [rev, hN _ h])
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  let g : ℕ × ℕ × ℤ → AssocState := fun (i,j,p) =>
    (-((-1 : ℂ) ^ (i+j))) •
      (dividedTranslation orbT i (F p) ⊗ₜ[ℂ]
        dividedTranslation planeT j (G ((i : ℤ) + j - 2 - p)))
  have g_support {i j : ℕ} {p : ℤ} (h : g (i,j,p) ≠ 0) :
      i + j < K ∧ (-1 - N ≤ p ∧ p ≤ M - 1) := by
    have hp : p < M := lt_of_not_ge fun hp => h (by simp [g, hM p hp])
    have hq : (i : ℤ) + j - 2 - p < N :=
      lt_of_not_ge fun hq => h (by simp [g, hN _ hq])
    dsimp [K]
    omega
  have gFinite : Function.HasFiniteSupport g := by
    refine (((Finset.range K) ×ˢ (Finset.range K) ×ˢ
      (Finset.Icc (-1-N) (M-1))).finite_toSet).subset ?_
    rintro ⟨i,j,p⟩ hp
    obtain ⟨hk, hp⟩ := g_support hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
    exact ⟨by omega, by omega, hp⟩
  let shift : ℤ × ℕ × ℕ ≃ ℕ × ℕ × ℤ :=
    { toFun := fun (p,i,j) => (i,j,p+i)
      invFun := fun (i,j,p) => (p-i,i,j)
      left_inv := by rintro ⟨p,i,j⟩; simp
      right_inv := by rintro ⟨i,j,p⟩; simp }
  let left (p : ℤ) (i j : ℕ) :=
    (epsilon (p+i+1) • dividedTranslation orbT i (F (p+i))) ⊗ₜ[ℂ]
      ((-epsilon (-2-p+j+1)) • dividedTranslation planeT j (G (-2-p+j)))
  have hshift (p : ℤ) (i j : ℕ) : left p i j = g (shift (p,i,j)) := by
    dsimp [left, g, shift]
    rw [show (i : ℤ) + j - 2 - (p+i) = -2-p+j by ring]
    simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, neg_mul]
    rw [epsilon, epsilon, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_natCast]
    rw [show -2 - p + (j : ℤ) + 1 + (p + (i : ℤ) + 1) = ((i+j : ℕ) : ℤ) by
      push_cast; ring]
  have hleft : ((assocY (a ⊗ₜ[ℂ] x))[[-1]]) (b ⊗ₜ[ℂ] y) = ∑ᶠ r, g (shift r) := by
    rw [finsum_curry₃ _ (Function.HasFiniteSupport.fun_comp_of_injective shift.injective gFinite),
      assocY_tmul]
    apply finsum_congr
    intro p
    rw [orb_skew a b p, show (-1 : ℤ) - 1 - p = -2-p by omega, plane_skew x y hx hy (-2-p)]
    let U (i : ℕ) := epsilon (p+i+1) • dividedTranslation orbT i (F (p+i))
    let W (j : ℕ) := (-epsilon (-2-p+j+1)) • dividedTranslation planeT j (G (-2-p+j))
    have fU : Function.HasFiniteSupport U := by
      refine (Finset.range (M-p).toNat).finite_toSet.subset ?_
      intro i hi
      exact Finset.mem_range.mpr (lt_of_not_ge fun h => hi (by simp [U, hM (p+i) (by omega)]))
    have fW : Function.HasFiniteSupport W := by
      refine (Finset.range (N+2+p).toNat).finite_toSet.subset ?_
      intro j hj
      exact Finset.mem_range.mpr (lt_of_not_ge fun h => hj (by simp [W, hN (-2-p+j) (by omega)]))
    change ((TensorProduct.mk ℂ Orbifold PlaneGhost).flip (∑ᶠ j, W j)) (∑ᶠ i, U i) = _
    rw [map_finsum _ fU]
    apply finsum_congr
    intro i
    change (TensorProduct.mk ℂ Orbifold PlaneGhost (U i)) (∑ᶠ j, W j) = _
    rw [map_finsum _ fW]
    exact finsum_congr fun j => hshift p i j
  rw [hleft, finsum_comp_equiv]
  let grouped : ℕ × ℕ → AssocState := fun (i,j) => ∑ᶠ p, g (i,j,p)
  calc
    (∑ᶠ r, g r) = ∑ᶠ ij, grouped ij := by
      let e : (ℕ × ℕ × ℤ) ≃ ((ℕ × ℕ) × ℤ) := (Equiv.prodAssoc ℕ ℕ ℤ).symm
      have finite := Function.HasFiniteSupport.fun_comp_of_injective e.symm.injective gFinite
      rw [← finsum_comp_equiv e.symm, finsum_curry _ finite]
      rfl
    _ = ∑ s ∈ Finset.range K, ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal s, grouped ij :=
      finsum_by_total grouped K fun i j h => finsum_eq_zero_of_forall_eq_zero fun p =>
        by by_contra hn; exact (not_lt_of_ge h) (g_support hn).1
    _ = _ := by
      rw [finsum_eq_sum_of_support_subset _ (s := Finset.range K) (by
        intro s hs
        apply Finset.mem_range.mpr
        by_contra h
        apply hs
        dsimp only
        rw [assocY_tmul]
        have hz : (∑ᶠ p, F p ⊗ₜ[ℂ] G ((s : ℤ) - 1 - 1 - p)) = 0 := by
          apply finsum_eq_zero_of_forall_eq_zero
          intro p
          by_cases hp : M ≤ p
          · simp [hM p hp]
          · simp [hN ((s : ℤ) - 1 - 1 - p) (by dsimp [K] at h; omega)]
        rw [hz, map_zero, smul_zero])]
      apply Finset.sum_congr rfl
      intro s hs
      rw [assocY_tmul]
      change (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal s, grouped ij) =
        (-((-1 : ℂ)^s)) • dividedTranslation assocT s (∑ᶠ p, rev s p)
      rw [map_finsum _ (revFinite s), smul_finsum' _ ((revFinite s).fun_comp (map_zero _))]
      change (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal s, ∑ᶠ p, g (ij.1, ij.2, p)) = _
      rw [sum_finsum_comm _ _ (fun ij _ => by
        exact Function.HasFiniteSupport.fun_comp_of_injective
          (g := fun p : ℤ => (ij.1, ij.2, p)) (fun _ _ h => congrArg (fun r => r.2.2) h) gFinite)]
      apply finsum_congr
      intro p
      dsimp only [rev]
      rw [divided_assoc_translation, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro ij hij
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have he' : (ij.1 : ℤ) + ij.2 - 2 - p = (s : ℤ) - 1 - 1 - p := by omega
      simp only [g, he, he']

private def assocSkewTerm (u v : AssocState) (s : ℕ) : AssocState :=
  (-((-1 : ℂ)^s)) • dividedTranslation assocT s (((assocY v)[[(s : ℤ)-1]]) u)

private theorem assoc_skew_finite (u v : AssocState) :
    Function.HasFiniteSupport (assocSkewTerm u v) := by
  obtain ⟨M, hM⟩ := term_truncation v u
  refine (Finset.range (M+1).toNat).finite_toSet.subset ?_
  intro s hs
  apply Finset.mem_range.mpr
  by_contra h
  apply hs
  have hz : ((assocY v)[[(s : ℤ)-1]]) u = 0 := by
    rw [assocY_modes]
    exact finsum_eq_zero_of_forall_eq_zero (hM _ (by omega))
  simp [assocSkewTerm, hz]

private def oddPart : Module.End ℂ PlaneGhost := (2 : ℂ)⁻¹ • (1 - par)

private theorem oddPart_odd (x : PlaneGhost) : par (oddPart x) = -oddPart x := by
  change par ((2 : ℂ)⁻¹ • (x - par x)) = -((2 : ℂ)⁻¹ • (x - par x))
  rw [map_smul, map_sub, parity_square, ← smul_neg, neg_sub]

private theorem assoc_projected_skew (u v : AssocState) :
    let P := rightLift oddPart
    ((assocY (P u))[[-1]]) (P v) = ∑ᶠ s, assocSkewTerm (P u) (P v) s := by
  dsimp only
  induction u using TensorProduct.inductionOn with
  | tmul a x =>
    induction v using TensorProduct.inductionOn with
    | tmul b y =>
      rw [rightLift_tmul, rightLift_tmul]
      exact assoc_tmul_skew a b (oddPart x) (oddPart y) (oddPart_odd x) (oddPart_odd y)
    | add v w hv hw =>
      simp only [map_add, hv, hw]
      simp only [assocSkewTerm, map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
      exact (finsum_add_distrib (assoc_skew_finite _ _) (assoc_skew_finite _ _)).symm
  | add u w hu hw =>
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, hu, hw]
    simp only [assocSkewTerm, map_add, smul_add]
    exact (finsum_add_distrib (assoc_skew_finite _ _) (assoc_skew_finite _ _)).symm

private theorem odd_part_reassoc (u : ComplexState) (hu : Degree 1 u) :
    rightLift oddPart (reassoc u) = reassoc u := by
  have hp : assocParity (reassoc u) = -reassoc u := by
    rw [← reassoc_parity, odd_of_degree_one hu]
    exact reassoc.map_neg u
  have h : rightLift oddPart = (2 : ℂ)⁻¹ • (1 - assocParity) := by
    simp only [oddPart, assocParity, map_smul, map_sub, map_one]
  rw [h, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, hp]
  module

private theorem reassoc_divided_translation (s : ℕ) (x : ComplexState) :
    reassoc (dividedTranslation T s x) = dividedTranslation assocT s (reassoc x) := by
  simp only [dividedTranslation, LinearMap.smul_apply, map_smul]
  congr 1
  induction s with
  | zero => rfl
  | succ s hs =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, reassoc_T, hs]

/-- The native odd product has the finite signed translation correction at mode -1. -/
theorem odd_product_skew : OddProductSkewLaw := by
  intro u v hu hv
  have h := assoc_projected_skew (reassoc u) (reassoc v)
  dsimp only at h
  rw [odd_part_reassoc u hu, odd_part_reassoc v hv] at h
  have ht (k : ℕ) :
      reassoc (skewCorrection u v k) = assocSkewTerm (reassoc u) (reassoc v) (k+1) := by
    calc
      reassoc (skewCorrection u v k) =
          reassoc ((-((-1 : ℂ) ^ (k+1))) •
            dividedTranslation T (k+1) (originalMode (k : ℤ) v u)) := by
        simp only [skewCorrection, skewCoefficient, dividedTranslation, LinearMap.smul_apply,
          div_eq_mul_inv, smul_smul]
      _ = _ := by
        simp only [map_smul, reassoc_divided_translation, reassoc_originalMode,
          assocSkewTerm, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  have ft := assoc_skew_finite (reassoc u) (reassoc v)
  have ftSucc := Function.HasFiniteSupport.fun_comp_of_injective Nat.succ_injective ft
  have split : (∑ᶠ s, assocSkewTerm (reassoc u) (reassoc v) s) =
      assocSkewTerm (reassoc u) (reassoc v) 0 +
        ∑ᶠ k : ℕ, assocSkewTerm (reassoc u) (reassoc v) (k+1) := by
    let e : Option ℕ ≃ ℕ :=
      { toFun := fun o => o.elim 0 Nat.succ
        invFun := fun k => Nat.casesOn k none some
        left_inv := by intro o; cases o <;> rfl
        right_inv := by intro k; cases k <;> rfl }
    have fs : Function.HasFiniteSupport
        ((fun o => assocSkewTerm (reassoc u) (reassoc v) (e o)) ∘ Option.some) := ftSucc
    rw [← finsum_comp_equiv e, finsum_option fs]
    rfl
  have f : Function.HasFiniteSupport (skewCorrection u v) := by
    refine ftSucc.subset ?_
    intro k hk hk'
    change assocSkewTerm (reassoc u) (reassoc v) k.succ = 0 at hk'
    exact hk (reassoc.injective ((ht k).trans (hk'.trans reassoc.map_zero.symm)))
  have hz : assocSkewTerm (reassoc u) (reassoc v) 0 =
      -(((assocY (reassoc v))[[-1]]) (reassoc u)) := by
    let z : AssocState := ((assocY (reassoc v))[[-1]]) (reassoc u)
    change (-((-1 : ℂ)^0)) • dividedTranslation assocT 0 z = -z
    simp only [pow_zero, dividedTranslation, Nat.factorial_zero, Nat.cast_one, inv_one,
      one_smul, Module.End.one_apply]
    exact neg_one_smul ℂ z
  have hmap := map_finsum reassoc.toLinearMap f
  change reassoc (∑ᶠ k, skewCorrection u v k) = ∑ᶠ k, reassoc (skewCorrection u v k) at hmap
  apply reassoc.injective
  rw [reassoc.map_add, reassoc_originalMode, reassoc_originalMode, h, split, hz, hmap,
    finsum_congr ht]
  abel

end NativeSkew

/-- A term of the absolute primitive, with j=k+1. -/
def skewPrimitiveTerm (u v : ComplexState) (k : ℕ) : ComplexState :=
  skewCoefficient k • B ((T ^ k) (originalMode (k : ℤ) v u))

/-- The skew primitive lives in the kernel of the original b0 on the relative shell. -/
def skewPrimitive (u v : ComplexState) : ComplexState :=
  -b0 (∑ᶠ k : ℕ, skewPrimitiveTerm u v k)

private theorem skew_support (u v : ComplexState) :
    ∃ M : ℕ, (∀ k ≥ M, skewPrimitiveTerm u v k = 0) ∧
      (∀ k ≥ M, skewCorrection u v k = 0) := by
  obtain ⟨M, hM⟩ := mode_tail v u
  exact ⟨M, fun k hk => by simp [skewPrimitiveTerm, hM k hk],
    fun k hk => by simp [skewCorrection, hM k hk]⟩

private theorem sum_skew {f : ℕ → ComplexState} (M : ℕ) (hf : ∀ k ≥ M, f k = 0) :
    (∑ᶠ k : ℕ, f k) = ∑ k ∈ Finset.range M, f k := by
  apply finsum_eq_sum_of_support_subset
  intro k hk
  apply Finset.mem_range.mpr
  exact lt_of_not_ge (fun h => hk (hf k h))

private theorem translated_mode
    {p q : Charge hyperbolicPlane} {u v : ComplexState}
    (pu : Momentum p u) (pv : Momentum q v) (du : Degree 1 u) (dv : Degree 1 v)
    (bu : b0 u = 0) (bv : b0 v = 0) (qu : Q u = 0) (qv : Q v = 0) (k l : ℕ) :
    let z := (T ^ l) (originalMode (k : ℤ) v u)
    Q z = 0 ∧ E z = (((l : ℤ) - (k + 1) : ℤ) : ℂ) • z ∧
      Degree 2 z ∧ Momentum (p + q) z := by
  induction l with
  | zero =>
    simp only [pow_zero, Module.End.one_apply]
    have hd : Degree (1 + 1) (originalMode (k : ℤ) v u) :=
      degree_mode (k : ℤ) (x := v) (y := u) dv du
    refine ⟨mode_closed (k : ℤ) qv qu, ?_, hd, ?_⟩
    · simpa only [Nat.cast_zero, zero_sub, Int.cast_neg] using energy_mode (k : ℤ) bv bu qv qu
    · exact (add_comm q p) ▸ momentum_mode (k : ℤ) pv pu
  | succ l ih =>
    simp only [pow_succ', Module.End.mul_apply]
    obtain ⟨hq, he, hn, hp⟩ := ih
    refine ⟨by rw [Q_T, hq, map_zero], ?_, degree_T hn, momentum_T hp⟩
    rw [E_T, he, map_smul]
    have hcast : (((l.succ : ℕ) : ℤ) - ((k : ℤ) + 1) : ℤ) =
        ((l : ℤ) - ((k : ℤ) + 1) : ℤ) + 1 := by omega
    rw [hcast, Int.cast_add, Int.cast_one, add_smul, one_smul]

private theorem skew_term_properties
    {p q : Charge hyperbolicPlane} {u v : ComplexState}
    (pu : Momentum p u) (pv : Momentum q v) (du : Degree 1 u) (dv : Degree 1 v)
    (bu : b0 u = 0) (bv : b0 v = 0) (qu : Q u = 0) (qv : Q v = 0) (k : ℕ) :
    Q (skewPrimitiveTerm u v k) = skewCorrection u v k ∧
      E (skewPrimitiveTerm u v k) = 0 ∧ Degree 1 (skewPrimitiveTerm u v k) ∧
      Momentum (p + q) (skewPrimitiveTerm u v k) := by
  let z := (T ^ k) (originalMode (k : ℤ) v u)
  obtain ⟨hq, he, hd, hp⟩ := translated_mode pu pv du dv bu bv qu qv k k
  change Q z = 0 at hq
  change Degree 2 z at hd
  change Momentum (p + q) z at hp
  change Q (skewCoefficient k • B z) = _ ∧ E (skewCoefficient k • B z) = 0 ∧
    Degree 1 (skewCoefficient k • B z) ∧ Momentum (p + q) (skewCoefficient k • B z)
  have hE : E (B z) = 0 := by
    rw [E_b, he, show ((k : ℤ) - ((k : ℤ) + 1) : ℤ) = -1 by omega, map_smul, sub_self]
  have hQz : Q (B z) = T z := by
    have h : Q (B z) + B (Q z) = T z := ward (-1) z
    simpa only [hq, map_zero, add_zero] using h
  have hn := degree_b (-1) hd
  have hm : Momentum (p + q) (B z) := momentum_b (-1) hp
  refine ⟨?_, by rw [map_smul, hE, smul_zero], ?_, ?_⟩
  · rw [map_smul, hQz, skewCorrection, pow_succ', Module.End.mul_apply]
  · simpa only [Degree, show (2 - 1 : ℤ) = 1 by norm_num, map_smul, smul_comm (skewCoefficient k)]
      using congrArg (fun w : ComplexState => skewCoefficient k • w) hn
  · unfold Momentum at hm ⊢
    simp only [map_smul, hm]

/-- The termwise translation homotopy, followed by -b0, gives an actual relative boundary. -/
theorem skew_boundary
    (hS : OddProductSkewLaw) {p q : Charge hyperbolicPlane} {u v : ComplexState}
    (hu : reassoc u ∈ relativeShell p) (hv : reassoc v ∈ relativeShell q)
    (du : Degree 1 u) (dv : Degree 1 v) (qu : Q u = 0) (qv : Q v = 0) :
    reassoc (skewPrimitive u v) ∈ relativeShell (p + q) ∧ Degree 0 (skewPrimitive u v) ∧
      Q (skewPrimitive u v) = current u v + current v u := by
  obtain ⟨pu, bu, _⟩ := (relative_iff p u).mp hu
  obtain ⟨pv, bv, _⟩ := (relative_iff q v).mp hv
  obtain ⟨M, hP, hR⟩ := skew_support u v
  let A := ∑ k ∈ Finset.range M, skewPrimitiveTerm u v k
  have hterm := skew_term_properties pu pv du dv bu bv qu qv
  have hA : skewPrimitive u v = -b0 A := by rw [skewPrimitive, sum_skew M hP]
  have hAQ : Q A = originalMode (-1) u v + originalMode (-1) v u := by
    rw [hS u v du dv, sum_skew M hR]
    simp only [A, map_sum]
    exact Finset.sum_congr rfl (fun k _ => (hterm k).1)
  have hAE : E A = 0 := by
    have term_energy (k : ℕ) : E (skewPrimitiveTerm u v k) = 0 := (hterm k).2.1
    simp only [A, map_sum, term_energy, Finset.sum_const_zero]
  have hAN : Degree 1 A := by
    have hd (k : ℕ) := (hterm k).2.2.1
    simp only [Degree, A, map_sum, Finset.smul_sum] at hd ⊢
    exact Finset.sum_congr rfl (fun k _ => hd k)
  have hAP : Momentum (p + q) A := by
    let g : ComplexState →ₗ[ℂ] AssocState := reassoc.toLinearMap
    let f : ComplexState →ₗ[ℂ] AssocState := (rightLift (chargeProject (p + q))).comp g
    let terms : ℕ → ComplexState := skewPrimitiveTerm u v
    change f (∑ k ∈ Finset.range M, terms k) = g (∑ k ∈ Finset.range M, terms k)
    exact (map_sum f terms (Finset.range M)).trans
      ((Finset.sum_congr rfl (fun k _ => (hterm k).2.2.2)).trans
        (map_sum g terms (Finset.range M)).symm)
  have hBP := momentum_b 0 hAP
  have hBN := degree_b 0 hAN
  refine ⟨(relative_iff _ _).mpr ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hA]
    let f := rightLift (chargeProject (p + q))
    let z : ComplexState := b0 A
    change f (reassoc (-z)) = reassoc (-z)
    exact (congrArg f (reassoc.map_neg z)).trans
      ((f.map_neg (reassoc z)).trans
        ((congrArg Neg.neg hBP).trans (reassoc.map_neg z).symm))
  · rw [hA, map_neg, ghost_square 0 A, neg_zero]
  · rw [hA, map_neg, E_b 0, hAE]
    simp only [map_zero, Int.cast_zero, zero_smul, sub_zero, neg_zero]
  · simpa only [hA, Degree, sub_self, map_neg, smul_neg, neg_inj] using hBN
  · have h := ward 0 A
    rw [hAE, hAQ, map_add, b0_product bu bv, b0_product bv bu] at h
    rw [hA, map_neg]
    have hn : Q (b0 A) = -(current u v + current v u) := eq_neg_of_add_eq_zero_left h
    exact (congrArg Neg.neg hn).trans (neg_neg _)

/-- The even (0,0,0) identity on the two extracted currents suffices. -/
abbrev EvenCurrentLaw : Prop :=
  ∀ (u v w : ComplexState), Degree 1 u → Degree 1 v →
    originalMode 0 (B u) (originalMode 0 (B v) w) =
      originalMode 0 (originalMode 0 (B u) (B v)) w +
        originalMode 0 (B v) (originalMode 0 (B u) w)

/-- The mode-zero extraction of the current is an exact state identity. -/
theorem B_current (u v : ComplexState) (du : Degree 1 u) :
    B (current u v) = originalMode 0 (B u) (B v) := by
  change B (originalMode 0 (B u) v) = _
  rw [actual_b_minus_one_mode, ghost_square (-1) u, even_B_of_degree_one du]
  simp only [map_zero, LinearMap.zero_apply, zero_add]

/-- The even (0,0,0) commutator gives left-Leibniz before passage to the quotient. -/
theorem current_leftLeibniz (hL : EvenCurrentLaw) (u v w : ComplexState)
    (du : Degree 1 u) (dv : Degree 1 v) :
    current u (current v w) = current (current u v) w + current v (current u w) := by
  change originalMode 0 (B u) (originalMode 0 (B v) w) =
    originalMode 0 (B (current u v)) w + originalMode 0 (B v) (originalMode 0 (B u) w)
  rw [B_current u v du]
  exact hL u v w du dv

/-- The two representatives of the skew defect define the zero class in the
common output shell. This form avoids a cast between p+q and q+p. -/
theorem skew_defect_class_zero (hS : OddProductSkewLaw)
    {p q : Charge hyperbolicPlane} (u : Cycles p 1) (v : Cycles q 1)
    (z : Cycles (p + q) 1)
    (hz : nativeValue z = current (nativeValue u) (nativeValue v) +
      current (nativeValue v) (nativeValue u)) :
    (Submodule.Quotient.mk z : Coh (p + q) 1) = 0 := by
  obtain ⟨h, d, w⟩ := skew_boundary hS (native_mem u) (native_mem v)
    (native_degree u) (native_degree v) (native_closed u) (native_closed v)
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (boundary_of_native z _ h d (w.trans hz.symm))

/-- A cyclic Jacobi witness, in a single pinned output shell with no momentum casts. -/
theorem jacobi_boundary (hS : OddProductSkewLaw) (hL : EvenCurrentLaw)
    {p q r : Charge hyperbolicPlane} {u v w : ComplexState}
    (hu : reassoc u ∈ relativeShell p) (hv : reassoc v ∈ relativeShell q)
    (hw : reassoc w ∈ relativeShell r)
    (du : Degree 1 u) (dv : Degree 1 v) (dw : Degree 1 w)
    (qu : Q u = 0) (qv : Q v = 0) (qw : Q w = 0) :
    ∃ a : ComplexState, reassoc a ∈ relativeShell (p + q + r) ∧ Degree 0 a ∧
      Q a = current u (current v w) + current v (current w u) + current w (current u v) := by
  obtain ⟨hUV, dUV, qUV⟩ := current_closed hu hv du dv qu qv
  obtain ⟨hs, ds, qs⟩ := skew_boundary hS hw hu dw du qw qu
  obtain ⟨ht, dt, qt⟩ := skew_boundary hS hUV hw dUV dw qUV qw
  obtain ⟨hs', ds', qs'⟩ := right_boundary hv hs dv ds qv
  have hp : q + (r + p) = p + q + r := by abel
  rw [hp] at hs'
  refine ⟨current v (skewPrimitive w u) + skewPrimitive (current u v) w, ?_, ?_, ?_⟩
  · rw [map_add]
    exact (relativeShell (p + q + r)).add_mem hs' ht
  · have hsN : N (current v (skewPrimitive w u)) = 0 := by
      simpa only [Degree, Int.cast_zero, zero_smul] using ds'
    have htN : N (skewPrimitive (current u v) w) = 0 := by
      simpa only [Degree, Int.cast_zero, zero_smul] using dt
    simp only [Degree, map_add, hsN, htN, Int.cast_zero, zero_smul, add_zero]
  · rw [map_add, qs', qt, qs, map_add, current_leftLeibniz hL u v w du dv]
    abel

/-- Every class represented by the cyclic Jacobi defect is zero. -/
theorem jacobi_defect_class_zero (hS : OddProductSkewLaw) (hL : EvenCurrentLaw)
    {p q r : Charge hyperbolicPlane} (u : Cycles p 1) (v : Cycles q 1) (w : Cycles r 1)
    (z : Cycles (p + q + r) 1)
    (hz : nativeValue z =
      current (nativeValue u) (current (nativeValue v) (nativeValue w)) +
      current (nativeValue v) (current (nativeValue w) (nativeValue u)) +
      current (nativeValue w) (current (nativeValue u) (nativeValue v))) :
    (Submodule.Quotient.mk z : Coh (p + q + r) 1) = 0 := by
  obtain ⟨a, hs, hd, hq⟩ := jacobi_boundary hS hL (native_mem u) (native_mem v) (native_mem w)
    (native_degree u) (native_degree v) (native_degree w)
    (native_closed u) (native_closed v) (native_closed w)
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (boundary_of_native z a hs hd (hq.trans hz.symm))

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
