/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldOriginalModes
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldOriginalModes
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Original Leech orbifold tensor modes, antighost Ward identities and BRST current. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTCurrentIdentities

/-!
The coefficient construction of LatticeMatterGhostStateField is applied to
the assembled orbifold field and the existing plane–ghost field. Truncation
is on evaluated states. On simple tensors each coefficient is captured by
an integer interval, and finite support extends through the tensor relations.

proof_shape: assocY, actual_b0_mode, actual_b_minus_one_mode, actualQ_current_zero_mode: content
admission_basis: escape-witness
escape_witness: The orbifold truncation bounds the convolution, the plane–ghost
antighost laws pass through each term, and the actual charge is recovered
using its statewise finite capture.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST

open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldMatter (Orbifold leechUnit leechPosDef)
open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane matter)
open LatticeMatterGhostCoupling (ghostB)
open LatticeSugawaraCurrents (gramComplex)
open TwistedGround.Orbifold
open D5.S3.Quantum.Fermionic
open D5.S3.Quantum.Fermionic.CountableOccupationFock (ket)
open private left_vacuum_modes from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField
open private antighost_mode from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyBVSecondOrder
open private rightLift_tmul from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone

private abbrev PlaneGhost := LatticeMatterGhostCoupling.State hyperbolicPlane
private abbrev orbY := OriginalOrbifoldField.Y leechData leechUnit leechPosDef
private abbrev planeY := LatticeMatterGhostStateField.Y hyperbolicPlane
private abbrev orbVacuum := OriginalOrbifoldField.vacuumState leechData leechUnit
private abbrev planeVacuum := LatticeAllStateField.vacuum hyperbolicPlane

private def term (n k : ℤ) : AssocState →ₗ[ℂ] Module.End ℂ AssocState :=
  TensorProduct.map₂
    ((LinearMap.proj k).comp (VertexOperator.ncoeff.comp orbY))
    ((LinearMap.proj (n - 1 - k)).comp (VertexOperator.ncoeff.comp planeY))

private theorem term_tmul (n k : ℤ) (u v : Orbifold) (a b : PlaneGhost) :
    term n k (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b) =
      ((orbY u)[[k]]) v ⊗ₜ[ℂ] ((planeY a)[[n - 1 - k]]) b := rfl

private theorem orb_tail (u v : Orbifold) :
    ∃ M : ℤ, ∀ k ≥ M, ((orbY u)[[k]]) v = 0 := by
  obtain ⟨M, hM⟩ := OriginalOrbifoldField.mode_tail leechData leechUnit leechPosDef u v
  exact ⟨M, fun k hk => by
    rw [OriginalOrbifoldField.Y_ncoeff]
    exact hM k hk⟩

private theorem term_support (u v : Orbifold) (a b : PlaneGhost) (n M G : ℤ)
    (hm : ∀ k ≥ M, ((orbY u)[[k]]) v = 0)
    (hg : ∀ k ≥ G, ((planeY a)[[k]]) b = 0) :
    Function.support (fun k => term n k (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b)) ⊆
      (↑(Finset.Icc (n - G) (M - 1)) : Set ℤ) := by
  intro k hk
  by_contra h
  have hd : k < n - G ∨ M - 1 < k := by
    simpa only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] using h
  apply hk
  dsimp only
  rw [term_tmul]
  rcases hd with hd | hd
  · rw [hg _ (by omega), TensorProduct.tmul_zero]
  · rw [hm _ (by omega), TensorProduct.zero_tmul]

private theorem term_finite (s x : AssocState) (n : ℤ) :
    Function.HasFiniteSupport (fun k : ℤ => term n k s x) := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    induction x using TensorProduct.inductionOn with
    | tmul v b =>
      obtain ⟨M, hm⟩ := orb_tail u v
      obtain ⟨G, hg⟩ := LatticeMatterGhostStateField.stateField_truncation hyperbolicPlane a b
      exact (Finset.Icc (n - G) (M - 1)).finite_toSet.subset (term_support u v a b n M G hm hg)
    | add x y hx hy =>
      simpa only [map_add, Pi.add_def] using hx.add hy
  | add s t hs ht =>
    simpa only [map_add, LinearMap.add_apply, Pi.add_def] using hs.add ht

private theorem term_truncation (s x : AssocState) :
    ∃ N : ℤ, ∀ n ≥ N, ∀ k : ℤ, term n k s x = 0 := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    induction x using TensorProduct.inductionOn with
    | tmul v b =>
      obtain ⟨M, hm⟩ := orb_tail u v
      obtain ⟨G, hg⟩ := LatticeMatterGhostStateField.stateField_truncation hyperbolicPlane a b
      refine ⟨M + G, fun n hn k => ?_⟩
      rw [term_tmul]
      by_cases hk : M ≤ k
      · rw [hm k hk, TensorProduct.zero_tmul]
      · rw [hg (n - 1 - k) (by omega), TensorProduct.tmul_zero]
    | add x y hx hy =>
      obtain ⟨N, hN⟩ := hx
      obtain ⟨P, hP⟩ := hy
      exact ⟨max N P, fun n hn k => by
        rw [map_add, hN n (by omega) k, hP n (by omega) k, add_zero]⟩
  | add s t hs ht =>
    obtain ⟨N, hN⟩ := hs
    obtain ⟨P, hP⟩ := ht
    exact ⟨max N P, fun n hn k => by
      rw [map_add, LinearMap.add_apply, hN n (by omega) k, hP n (by omega) k, add_zero]⟩

private def coefficient (n : ℤ) : AssocState →ₗ[ℂ] Module.End ℂ AssocState where
  toFun s := {
    toFun x := ∑ᶠ k : ℤ, term n k s x
    map_add' x y := by
      simp only [map_add]
      exact finsum_add_distrib (term_finite s x n) (term_finite s y n)
    map_smul' z x := by
      simp only [map_smul, RingHom.id_apply]
      exact (smul_finsum' z (term_finite s x n)).symm }
  map_add' s t := by
    apply LinearMap.ext
    intro x
    change (∑ᶠ k : ℤ, term n k (s + t) x) =
      (∑ᶠ k : ℤ, term n k s x) + (∑ᶠ k : ℤ, term n k t x)
    simp only [map_add, LinearMap.add_apply]
    exact finsum_add_distrib (term_finite s x n) (term_finite t x n)
  map_smul' z s := by
    apply LinearMap.ext
    intro x
    change (∑ᶠ k : ℤ, term n k (z • s) x) = z • ∑ᶠ k : ℤ, term n k s x
    simp only [map_smul, LinearMap.smul_apply]
    exact (smul_finsum' z (term_finite s x n)).symm

private def field (s : AssocState) : VertexOperator ℂ AssocState :=
  VertexOperator.of_coeff (fun power => coefficient (-power - 1) s) (by
    intro x
    obtain ⟨N, hN⟩ := term_truncation s x
    refine ⟨-N, fun power hp => ?_⟩
    by_contra h
    exact hp (finsum_eq_zero_of_forall_eq_zero (hN (-power - 1) (by omega))))

private theorem field_modes (s : AssocState) (n : ℤ) :
    (field s)[[n]] = coefficient n s := by
  rw [field, VertexOperator.ncoeff_of_coeff, show -(-n - 1) - 1 = n by omega]

/-- The all-state field of the original orbifold and the original plane–ghost field. -/
def assocY : AssocState →ₗ[ℂ] VertexOperator ℂ AssocState where
  toFun := field
  map_add' s t := by
    apply HVertexOperator.coeff_inj
    funext power
    simp only [VertexOperator.coeff_eq_ncoeff, field_modes, map_add, Pi.add_apply]
  map_smul' z s := by
    apply HVertexOperator.coeff_inj
    funext power
    simp only [VertexOperator.coeff_eq_ncoeff, field_modes, map_smul, Pi.smul_apply,
      RingHom.id_apply]

private theorem assocY_modes (n : ℤ) (s x : AssocState) :
    ((assocY s)[[n]]) x = ∑ᶠ k : ℤ, term n k s x := by
  change ((field s)[[n]]) x = _
  rw [field_modes]
  rfl

private theorem assocY_tmul (n : ℤ) (u v : Orbifold) (a b : PlaneGhost) :
    ((assocY (u ⊗ₜ[ℂ] a))[[n]]) (v ⊗ₜ[ℂ] b) =
      ∑ᶠ k : ℤ, ((orbY u)[[k]]) v ⊗ₜ[ℂ] ((planeY a)[[n - 1 - k]]) b := by
  rw [assocY_modes]
  exact finsum_congr (fun k => term_tmul n k u v a b)

/-- Any two statewise mode bounds give the literal interval for the convolution. -/
theorem assocY_tmul_interval (n : ℤ) (u v : Orbifold) (a b : PlaneGhost) (M G : ℤ)
    (hm : ∀ k ≥ M, ((orbY u)[[k]]) v = 0)
    (hg : ∀ k ≥ G, ((planeY a)[[k]]) b = 0) :
    ((assocY (u ⊗ₜ[ℂ] a))[[n]]) (v ⊗ₜ[ℂ] b) =
      ∑ k ∈ Finset.Icc (n - G) (M - 1),
        ((orbY u)[[k]]) v ⊗ₜ[ℂ] ((planeY a)[[n - 1 - k]]) b := by
  rw [assocY_modes, finsum_eq_sum_of_support_subset _ (term_support u v a b n M G hm hg)]
  exact Finset.sum_congr rfl (fun k _ => term_tmul n k u v a b)

private def assocMode (n : ℤ) : AssocState →ₗ[ℂ] Module.End ℂ AssocState :=
  (LinearMap.proj n).comp (VertexOperator.ncoeff.comp assocY)

/-- The original convolution modes transported to the native BRST carrier. -/
def originalMode (n : ℤ) : ComplexState →ₗ[ℂ] Module.End ℂ ComplexState :=
  (reassoc.symm.conjAlgEquiv ℂ).toLinearMap.comp ((assocMode n).comp reassoc.toLinearMap)

theorem reassoc_originalMode (n : ℤ) (s x : ComplexState) :
    reassoc (originalMode n s x) = ((assocY (reassoc s))[[n]]) (reassoc x) := by
  change reassoc (reassoc.symm (((assocY (reassoc s))[[n]]) (reassoc x))) = _
  exact reassoc.apply_symm_apply _

private theorem assoc_vacuum_left (n : ℤ) (a : PlaneGhost) :
    ((assocY (orbVacuum ⊗ₜ[ℂ] a))[[n]]) = rightLift ((planeY a)[[n]]) := by
  apply TensorProduct.ext'
  intro v b
  rw [assocY_tmul]
  simp_rw [OriginalOrbifoldField.vacuum_ncoeff]
  rw [finsum_eq_single _ (-1)]
  · rw [ite_eq_left rfl, show n - 1 - -1 = n by omega, rightLift_tmul]
  · intro k hk
    rw [ite_eq_right hk, TensorProduct.zero_tmul]

private abbrev assocB (r : ℤ) := rightLift (ghostB hyperbolicPlane r)
private abbrev assocParity := rightLift (LatticeMatterGhostStateField.parity hyperbolicPlane)

/-- The bc parity on the original BRST carrier. -/
def originalParity : Module.End ℂ ComplexState :=
  (reassoc.symm.conjAlgEquiv ℂ) assocParity

private theorem reassoc_parity (x : ComplexState) :
    reassoc (originalParity x) = assocParity (reassoc x) := by
  change reassoc (reassoc.symm (assocParity (reassoc x))) = _
  exact reassoc.apply_symm_apply _

private theorem reassoc_ghostB (r : ℤ) (x : ComplexState) :
    reassoc (VirasoroBRST.ghostB matter r x) = assocB r (reassoc x) := by
  have h : reassoc.toLinearMap.comp (VirasoroBRST.ghostB matter r) =
      (assocB r).comp reassoc.toLinearMap := by
    apply TensorProduct.ext'
    intro v w
    induction v using TensorProduct.inductionOn with
    | tmul u a => rfl
    | add v z hv hz =>
      simp only [TensorProduct.add_tmul, map_add, hv, hz]
  exact LinearMap.congr_fun h x

/-- The antighost state with both literal matter vacua. -/
def originalAntighost : ComplexState :=
  reassoc.symm (orbVacuum ⊗ₜ[ℂ] (planeVacuum ⊗ₜ[ℂ] ket {0}))

/-- The normalized modes zero and one of this field are b(-1) and b0. -/
theorem originalAntighost_modes (n : ℤ) :
    originalMode n originalAntighost = VirasoroBRST.ghostB matter (n - 1) := by
  apply LinearMap.ext
  intro x
  apply reassoc.injective
  rw [reassoc_originalMode, originalAntighost, reassoc.apply_symm_apply, assoc_vacuum_left,
    left_vacuum_modes, BcGhostStateField.stateField_creation.2.2.2.1, reassoc_ghostB]
  rfl

private theorem plane_b_commutator (r n : ℤ) (hr : r = 0 ∨ r = -1) (s x : PlaneGhost) :
    ghostB hyperbolicPlane r (((planeY s)[[n]]) x) =
      ((planeY (ghostB hyperbolicPlane r s))[[n]]) x +
        ((r + 1 : ℤ) : ℂ) • ((planeY (ghostB hyperbolicPlane (-1) s))[[n + 1]]) x +
        ((planeY (LatticeMatterGhostStateField.parity hyperbolicPlane s))[[n]])
          (ghostB hyperbolicPlane r x) := by
  rcases hr with rfl | rfl
  · simpa only [LatticeBRSTCohomologyField.originalMode_apply,
      show ((0 + 1 : ℤ) : ℂ) = 1 by norm_num, one_smul] using
      sub_eq_iff_eq_add.mp (antighost_mode hyperbolicPlane s x n)
  · simpa only [LatticeBRSTCohomologyField.originalMode_apply,
      show ((-1 + 1 : ℤ) : ℂ) = 0 by norm_num, zero_smul, add_zero] using
      Lattice.PhysicalLie.LatticeBRSTCurrentIdentities.b_minus_one_mode hyperbolicPlane s x n

private theorem term_b_commutator (r n k : ℤ) (hr : r = 0 ∨ r = -1) (s : AssocState) :
    assocB r * term n k s =
      term n k (assocB r s) +
        ((r + 1 : ℤ) : ℂ) • term (n + 1) k (assocB (-1) s) +
        term n k (assocParity s) * assocB r := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    apply TensorProduct.ext'
    intro v b
    have h := congrArg (fun w : PlaneGhost => ((orbY u)[[k]]) v ⊗ₜ[ℂ] w)
      (plane_b_commutator r (n - 1 - k) hr a b)
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, term_tmul,
      rightLift_tmul, TensorProduct.tmul_add, TensorProduct.tmul_smul,
      show n - 1 - k + 1 = n + 1 - 1 - k by omega] at h ⊢
    exact h
  | add s t hs ht =>
    simp only [map_add, mul_add, add_mul, hs, ht, smul_add]
    abel

private theorem assoc_b_commutator (r n : ℤ) (hr : r = 0 ∨ r = -1) (s x : AssocState) :
    assocB r (((assocY s)[[n]]) x) =
      ((assocY (assocB r s))[[n]]) x +
        ((r + 1 : ℤ) : ℂ) • ((assocY (assocB (-1) s))[[n + 1]]) x +
        ((assocY (assocParity s))[[n]]) (assocB r x) := by
  let c : ℂ := ((r + 1 : ℤ) : ℂ)
  let first : ℤ → AssocState := fun k => term n k (assocB r s) x
  let correction : ℤ → AssocState := fun k => term (n + 1) k (assocB (-1) s) x
  let reverse : ℤ → AssocState := fun k => term n k (assocParity s) (assocB r x)
  have hf : Function.HasFiniteSupport first := term_finite (assocB r s) x n
  have hc : Function.HasFiniteSupport correction := term_finite (assocB (-1) s) x (n + 1)
  have hc' : Function.HasFiniteSupport (fun k => c • correction k) :=
    hc.smul_right (fun _ : ℤ => c)
  have hr' : Function.HasFiniteSupport reverse := term_finite (assocParity s) (assocB r x) n
  simp only [assocY_modes]
  change assocB r (∑ᶠ k : ℤ, term n k s x) =
    (∑ᶠ k : ℤ, first k) + c • (∑ᶠ k : ℤ, correction k) + ∑ᶠ k : ℤ, reverse k
  rw [map_finsum (assocB r) (term_finite s x n), smul_finsum' c hc,
    ← finsum_add_distrib hf hc',
    ← finsum_add_distrib (f := fun k => first k + c • correction k) (hf.add hc') hr']
  exact finsum_congr (fun k => LinearMap.congr_fun (term_b_commutator r n k hr s) x)

private theorem original_b_commutator (r n : ℤ) (hr : r = 0 ∨ r = -1) (s x : ComplexState) :
    VirasoroBRST.ghostB matter r (originalMode n s x) =
      originalMode n (VirasoroBRST.ghostB matter r s) x +
        ((r + 1 : ℤ) : ℂ) • originalMode (n + 1) (VirasoroBRST.ghostB matter (-1) s) x +
        originalMode n (originalParity s) (VirasoroBRST.ghostB matter r x) := by
  apply reassoc.injective
  simpa only [map_add, map_smul, reassoc_ghostB, reassoc_originalMode, reassoc_parity] using
    assoc_b_commutator r n hr (reassoc s) (reassoc x)

/-- The native beta mode one Ward identity, including its mode-shift term. -/
theorem actual_b0_mode (n : ℤ) (s x : ComplexState) :
    b0 (originalMode n s x) =
      originalMode n (b0 s) x +
        originalMode (n + 1) (VirasoroBRST.ghostB matter (-1) s) x +
        originalMode n (originalParity s) (b0 x) := by
  simpa only [show ((0 + 1 : ℤ) : ℂ) = 1 by norm_num, one_smul] using
    original_b_commutator 0 n (Or.inl rfl) s x

/-- The native beta mode zero Ward identity on every convolution mode. -/
theorem actual_b_minus_one_mode (n : ℤ) (s x : ComplexState) :
    VirasoroBRST.ghostB matter (-1) (originalMode n s x) =
      originalMode n (VirasoroBRST.ghostB matter (-1) s) x +
        originalMode n (originalParity s) (VirasoroBRST.ghostB matter (-1) x) := by
  simpa only [show ((-1 + 1 : ℤ) : ℂ) = 0 by norm_num, zero_smul, add_zero] using
    original_b_commutator (-1) n (Or.inr rfl) s x

/-- The literal BRST current with the split matter stress state and the original ghost cubic. -/
def assocBRSTCurrent : AssocState :=
  ActualLeechOrbifoldMatter.omega ⊗ₜ[ℂ] (planeVacuum ⊗ₜ[ℂ] ket {1}) +
    orbVacuum ⊗ₜ[ℂ] LatticeMatterGhostStateField.Jtot hyperbolicPlane (gramComplex hyperbolicPlane)

private theorem assoc_orbifold_current (v : Orbifold) (b : PlaneGhost) :
    ((assocY (ActualLeechOrbifoldMatter.omega ⊗ₜ[ℂ] (planeVacuum ⊗ₜ[ℂ] ket {1})))[[0]])
        (v ⊗ₜ[ℂ] b) =
      ∑ᶠ m : ℤ, orbifoldSummand m (v ⊗ₜ[ℂ] b) := by
  rw [assocY_tmul]
  let f : ℤ → AssocState := fun k =>
    ((orbY ActualLeechOrbifoldMatter.omega)[[k]]) v ⊗ₜ[ℂ]
      ((planeY (planeVacuum ⊗ₜ[ℂ] ket {1}))[[0 - 1 - k]]) b
  let e : ℤ ≃ ℤ := Equiv.addRight 1
  change (∑ᶠ k : ℤ, f k) = _
  calc
    _ = ∑ᶠ m : ℤ, f (e m) := (finsum_comp_equiv e).symm
    _ = _ := by
      apply finsum_congr
      intro m
      change ActualLeechOrbifoldMatter.mode m v ⊗ₜ[ℂ]
        ((planeY (planeVacuum ⊗ₜ[ℂ] ket {1}))[[0 - 1 - (m + 1)]]) b = _
      rw [left_vacuum_modes, BcGhostStateField.stateField_creation.2.2.2.2,
        show (0 - 1 - (m + 1) + 2 : ℤ) = -m by omega]
      rfl

/-- The literal current's zero mode equals the existing charge on the reassociated carrier. -/
theorem assocQ_current_zero_mode : ((assocY assocBRSTCurrent)[[0]]) = assocQ := by
  apply TensorProduct.ext'
  intro v b
  obtain ⟨indices, hs, hQ⟩ := assocQ_finite_capture (v ⊗ₜ[ℂ] b)
  conv_lhs =>
    simp only [assocBRSTCurrent, map_add, Pi.add_apply, LinearMap.add_apply,
      assoc_orbifold_current, assoc_vacuum_left, LatticeMatterGhostStateField.current_zero_mode]
  rw [finsum_eq_sum_of_support_subset _ hs, hQ]
  exact add_comm _ _

/-- The literal current as a state of the native BRST complex. -/
def actualBRSTCurrent : ComplexState := reassoc.symm assocBRSTCurrent

/-- Exact zero-mode identification with the native differential Q. -/
theorem actualQ_current_zero_mode : originalMode 0 actualBRSTCurrent = Q := by
  apply LinearMap.ext
  intro x
  apply reassoc.injective
  rw [reassoc_originalMode, actualBRSTCurrent, reassoc.apply_symm_apply, assocQ_current_zero_mode]
  change ((reassoc.conjAlgEquiv ℂ) Q) (reassoc x) = _
  rw [LinearEquiv.conjAlgEquiv_apply (R := ℂ) reassoc Q]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST
