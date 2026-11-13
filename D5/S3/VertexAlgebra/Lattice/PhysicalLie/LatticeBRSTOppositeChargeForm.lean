/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTOppositeChargeForm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTOppositeChargeForm
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: []
   utility: none
   digest: Opposite-charge bilinear inserted form on actual states and neutral descent. -/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeReflection
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTInsertedTailOrthogonality
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan

/-!
SOURCE ONLY, UNCOMPILED. The imported neutral classification is the sealed
terminal neutral43 CANDIDATE, also UNCOMPILED. In particular the neutral
quotient statements below inherit that pending status, not native acceptance.

This is the literal inserted(Cx,y), on State D, not an abstract BPZ surrogate.
It is symmetric and bilinear before passage to cohomology. The only quotient
form constructed here is its restriction to the NEUTRAL physical image using
the preserved neutral supplier. Global physical-image descent and invariance
remain obligations; they are not assumptions or conclusions of this file.

Attribution: the original lattice Wick form, occupation Hg, relativePartner,
eps and c0 retain their supplier attribution; the new tensor computation uses
Mathlib finite sums and the neutral candidate's actual classification.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct

open private slices slices_tmul slices_tmul_ket from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian
open private matterC conjugation_tmul_ket matterC_square from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeReflection

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeChargeForm

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField (vacuum)
open LatticeSugawaraCurrents LatticeMatterGhostCoupling
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeReflection (conjugation)
open SourceBPZ.OriginalSourcePairing SourceBPZ.OriginalMatterHermitian
open D5.S3.Quantum.Fermionic
open CountableOccupationFock BcGhostHermitian

variable {D : LatticeData}

/-- The desired state-level complex bilinear form, with the original c0.
No quotient or replacement bracket enters this definition. -/
def statePairing (D : LatticeData) : LinearMap.BilinForm ℂ (State D) where
  toFun x := {
    toFun y := inserted (conjugation D x) y
    map_add' y z := inserted_add_right _ y z
    map_smul' a y := inserted_smul_right a _ y }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    change inserted (conjugation D (x + z)) y = _
    simp only [map_add, inserted_add_left, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    change inserted (conjugation D (a • x)) y = _
    simp only [map_smulₛₗ, inserted_smul_left, starRingEnd_apply, star_star, LinearMap.smul_apply,
      smul_eq_mul, RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk]

private theorem state_expansion (x : State D) :
    (∑ S ∈ (slices D x).support, (slices D x) S ⊗ₜ[ℂ] ket S) = x := by
  classical
  apply (slices D).injective
  simp only [map_sum, slices_tmul_ket]
  exact Finsupp.sum_single _

private theorem pairing_tmul_ket (v w : Carrier D) (S T : Finset ℕ) :
    statePairing D (v ⊗ₜ[ℂ] ket S) (w ⊗ₜ[ℂ] ket T) =
      sourcePairing D v w * Hg (ket S) (BcGhostFock.c 0 (ket T)) := by
  change inserted (conjugation D (v ⊗ₜ[ℂ] ket S)) (w ⊗ₜ[ℂ] ket T) = _
  rw [conjugation_tmul_ket]
  change Hmg (matterC v ⊗ₜ[ℂ] ket S)
    (w ⊗ₜ[ℂ] BcGhostFock.c 0 (ket T)) = _
  rw [Hmg_tmul]
  change sourcePairing D (matterC (matterC v)) w * _ = _
  rw [matterC_square]

private theorem ghostInsertion_real (S T : Finset ℕ) :
    star (Hg (ket S) (BcGhostFock.c 0 (ket T))) =
      Hg (ket S) (BcGhostFock.c 0 (ket T)) := by
  rw [c_zero, create_ket]
  by_cases h : 3 ∈ T
  · simp [h]
  · simp only [if_neg h, Hg_smul_right, star_mul, phase_real]
    rw [Hg_ket_ket]
    split_ifs <;> rcases eps_sign S with hS | hS <;> simp [hS, phase_real]

private theorem ghostInsertion_symmetric (S T : Finset ℕ) :
    Hg (ket S) (BcGhostFock.c 0 (ket T)) =
      Hg (ket T) (BcGhostFock.c 0 (ket S)) := by
  calc
    _ = Hg (BcGhostFock.c 0 (ket S)) (ket T) := by
      simpa only [neg_zero] using (Hg_c 0 (ket S) (ket T)).symm
    _ = star (Hg (ket T) (BcGhostFock.c 0 (ket S))) := Hg_hermitian _ _
    _ = _ := ghostInsertion_real T S

private theorem pairing_slices (x y : State D) :
    statePairing D x y =
      ∑ S ∈ (slices D x).support, ∑ T ∈ (slices D y).support,
        sourcePairing D ((slices D x) S) ((slices D y) T) *
          Hg (ket S) (BcGhostFock.c 0 (ket T)) := by
  conv_lhs => rw [← state_expansion x, ← state_expansion y]
  simp only [map_sum, LinearMap.sum_apply, pairing_tmul_ket]
  rw [Finset.sum_comm]

/-- Symmetry is ordinary complex bilinear symmetry, with no ghost parity sign. -/
theorem statePairing_symmetric (x y : State D) :
    statePairing D x y = statePairing D y x := by
  rw [pairing_slices, pairing_slices, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro S hS
  rw [sourcePairing_symmetric D, ghostInsertion_symmetric]

private theorem slices_b0 (x : State D) (T : Finset ℕ) :
    slices D (ghostB D 0 x) T =
      if 3 ∈ T then 0 else phase 3 T • slices D x (insert 3 T) := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul v g =>
      change slices D (v ⊗ₜ[ℂ] BcGhostFock.b 0 g) T = _
      rw [slices_tmul, b_zero, annihilate_coefficient]
      by_cases h : 3 ∈ T <;>
        simp [h, slices_tmul, smul_smul, smul_eq_mul]
  | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply, hx, hy]
      split_ifs <;> simp [smul_add]

private theorem relative_slice (x : State D) (hx : ghostB D 0 x = 0)
    (S : Finset ℕ) (hS : 3 ∈ S) : slices D x S = 0 := by
  classical
  have h := slices_b0 x (S.erase 3)
  rw [hx, map_zero, Finsupp.zero_apply,
    if_neg (Finset.notMem_erase _ _), Finset.insert_erase hS] at h
  exact (smul_eq_zero.mp h.symm).resolve_left (phase_ne_zero _ _)

private theorem ghostInsertion_relative (S T : Finset ℕ) (hS : 3 ∉ S) :
    Hg (ket S) (BcGhostFock.c 0 (ket T)) =
      if T = relativePartner S then relativeEps S else 0 := by
  rw [Hg_ket_coefficient, c_zero, create_coefficient,
    if_pos (three_mem_partner S hS)]
  by_cases h : T = relativePartner S
  · simp [ket, h, relativePartner, relativeEps, mul_assoc]
  · have ht : T ≠ (partner S).erase 3 := h
    simp [ket, Finsupp.single_apply, ht, h]

/-- The finite occupation/charge formula on the literal relative carrier.
The second argument is unrestricted. Neither polynomial is conjugated.
The ghost sign is the original eps times the original c0 insertion phase. -/
theorem statePairing_relative_coefficients (x y : State D)
    (hx : ghostB D 0 x = 0) :
    statePairing D x y =
      ∑ S ∈ (slices D x).support, ∑ p ∈ ((slices D x) S).support,
        relativeEps S * integerWick D (((slices D x) S) p)
          (((slices D y) (relativePartner S)) (-p)) := by
  classical
  rw [pairing_slices]
  apply Finset.sum_congr rfl
  intro S hS
  have hthree : 3 ∉ S := by
    intro hs
    exact (Finsupp.mem_support_iff.mp hS) (relative_slice x hx S hs)
  simp_rw [ghostInsertion_relative S _ hthree]
  have collapse :
      (∑ T ∈ (slices D y).support,
        sourcePairing D ((slices D x) S) ((slices D y) T) *
          (if T = relativePartner S then relativeEps S else 0)) =
      relativeEps S * sourcePairing D ((slices D x) S)
        ((slices D y) (relativePartner S)) := by
    rw [Finset.sum_eq_single (relativePartner S)]
    · simp [mul_comm]
    · intro T hT hne
      simp [hne]
    · intro hnot
      have hz : (slices D y) (relativePartner S) = 0 :=
        Finsupp.notMem_support_iff.mp hnot
      simp [hz]
  rw [collapse]
  have expand :
      sourcePairing D ((slices D x) S) ((slices D y) (relativePartner S)) =
        ∑ p ∈ ((slices D x) S).support,
          integerWick D (((slices D x) S) p)
            (((slices D y) (relativePartner S)) (-p)) := by
    have hs := congrArg (fun u : Carrier D =>
      sourcePairing D u ((slices D y) (relativePartner S)))
      (Finsupp.sum_single ((slices D x) S))
    simp only [Finsupp.sum, map_sum, LinearMap.sum_apply, sourcePairing_single] at hs
    exact hs.symm
  rw [expand, Finset.mul_sum]

private theorem slices_chargeProject (p : Charge D) (x : State D) (S : Finset ℕ) :
    slices D (LatticeQuartetContraction.chargeProject p x) S =
      Finsupp.single p (((slices D x) S) p) := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul v g =>
      change slices D (Finsupp.single p (v p) ⊗ₜ[ℂ] g) S = _
      simp only [slices_tmul, Finsupp.smul_apply, ← Finsupp.smul_single]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, Finsupp.single_add]

/-- Charge p and charge q are orthogonal unless p+q=0, on actual original
states, including zero vectors and zero charge. No shell condition is used. -/
theorem statePairing_charge_orthogonal (p q : Charge D) (x y : State D)
    (hx : LatticeQuartetContraction.chargeProject p x = x)
    (hy : LatticeQuartetContraction.chargeProject q y = y) (hpq : p + q ≠ 0) :
    statePairing D x y = 0 := by
  classical
  have hqp : q ≠ -p := by
    intro h
    apply hpq
    rw [h, add_neg_cancel]
  rw [pairing_slices]
  apply Finset.sum_eq_zero
  intro S hS
  apply Finset.sum_eq_zero
  intro T hT
  have hxs : (slices D x) S = Finsupp.single p (((slices D x) S) p) := by
    simpa only [hx] using (slices_chargeProject p x S)
  have hyt : (slices D y) T = Finsupp.single q (((slices D y) T) q) := by
    simpa only [hy] using (slices_chargeProject q y T)
  rw [hxs, hyt, sourcePairing_single_single, if_neg hqp, zero_mul]

private theorem pairing_down (v w : Carrier D) :
    statePairing D (v ⊗ₜ[ℂ] ket {1}) (w ⊗ₜ[ℂ] ket {1}) =
      sourcePairing D v w := by
  rw [pairing_tmul_ket, D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTInsertedTailOrthogonality.Hg_down_c0_down, mul_one]

open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan
open private cartan_basis_tensor neutral_number_one_shell current_creation
  from D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan

private theorem current_gram (i j : Fin D.rank) :
    sourcePairing D (LatticeActualConformalState.currentState D i)
      (LatticeActualConformalState.currentState D j) = -(D.G i j : ℂ) := by
  have hcreate : neutralMode D i (-1) (vacuum D) =
      LatticeActualConformalState.currentState D i := by
    simpa only [LatticeAllStateField.vacuum] using current_creation D i
  have hann : neutralMode D i 1 (LatticeActualConformalState.currentState D j) =
      (D.G i j : ℂ) • vacuum D := by
    classical
    simp [LatticeActualConformalState.currentState, neutralMode,
      neutralPolynomialMode, weightedPartial, MvPolynomial.pderiv_X,
      LinearMap.sum_apply, LinearMap.smul_apply, LatticeAllStateField.vacuum,
      Pi.single_apply, Prod.mk.injEq, ← Finsupp.smul_single]
  rw [← hcreate,
    SourceBPZ.SourcePairingLaws.sourcePairing_neutralMode D i (-1), neg_neg, hann]
  simp [sourcePairing_vacuum]

/-- The neutral current Gram is MINUS G. This is a bilinear computation and
asserts no real positivity, even when G is positive definite. -/
theorem statePairing_cartan (e f : Fin D.rank → ℂ) :
    statePairing D (cartanState D e) (cartanState D f) =
      -∑ i : Fin D.rank, ∑ j : Fin D.rank, e i * (D.G i j : ℂ) * f j := by
  classical
  have hc (a : Fin D.rank → ℂ) : cartanState D a =
      ∑ i, a i • (LatticeActualConformalState.currentState D i ⊗ₜ[ℂ] ket {1}) := by
    simp only [cartanState, LinearMap.coe_mk, AddHom.coe_mk, cartan_basis_tensor]
  rw [hc e, hc f]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, cartan_basis_tensor, pairing_down, current_gram, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [show -(∑ i : Fin D.rank, ∑ j : Fin D.rank,
      e i * (D.G i j : ℂ) * f j) =
      ∑ i : Fin D.rank, ∑ j : Fin D.rank, -(e i * (D.G i j : ℂ) * f j) by
    simp only [Finset.sum_neg_distrib]]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

section NeutralDescent

variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
  (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

/-- The state form on the literal neutral submodule of the global physical
image. Its coordinate equivalence is the preserved UNCOMPILED neutral43
supplier; no replacement quotient or restriction on incoming primitives occurs. -/
def neutralImageForm : LinearMap.BilinForm ℂ
    (neutralPhysicalImage D H h26 hHG hGH) := by
  let E := neutralCartanEquiv D H h26 hHG hGH
  let A : (Fin D.rank → ℂ) →ₗ[ℂ] State D := cartanState D
  exact (statePairing D).compl₁₂ (A.comp E.symm.toLinearMap)
    (A.comp E.symm.toLinearMap)

/-- Recovery from arbitrary neutral physical representatives with equality
in the ORIGINAL GLOBAL quotient. All incoming global primitives are allowed.
This does not claim descent outside the neutral component. -/
theorem neutralImageForm_representatives
    (x y : neutralPhysicalImage D H h26 hHG hGH)
    (a b : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalStates D H)
    (ha0 : (a : State D) ∈ LatticeRelativeMassShell.fixedMomentum D 0)
    (hb0 : (b : State D) ∈ LatticeRelativeMassShell.fixedMomentum D 0)
    (ha : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalClass D H h26 hHG hGH a = x.val)
    (hb : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalClass D H h26 hHG hGH b = y.val) :
    neutralImageForm H h26 hHG hGH x y = statePairing D a b := by
  obtain ⟨e, he, _⟩ := neutral_number_one_shell D H hHG hGH a ha0
    a.property.2.1 a.property.2.2.1 a.property.2.2.2
  obtain ⟨f, hf, _⟩ := neutral_number_one_shell D H hHG hGH b hb0
    b.property.2.1 b.property.2.2.1 b.property.2.2.2
  let E := neutralCartanEquiv D H h26 hHG hGH
  have hec : E e = x := by
    apply Subtype.ext
    change D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalClass D H h26 hHG hGH
      (cartanRepresentative D H hHG hGH e) = x.val
    rw [show cartanRepresentative D H hHG hGH e = a from Subtype.ext he, ha]
  have hfc : E f = y := by
    apply Subtype.ext
    change D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalClass D H h26 hHG hGH
      (cartanRepresentative D H hHG hGH f) = y.val
    rw [show cartanRepresentative D H hHG hGH f = b from Subtype.ext hf, hb]
  change statePairing D (cartanState D (E.symm x)) (cartanState D (E.symm y)) = _
  rw [← hec, ← hfc, E.symm_apply_apply, E.symm_apply_apply, he, hf]

end NeutralDescent

-- Exact original-scope normalization checks stay anonymous, not named wrappers.
example (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    statePairing D (vacuum D ⊗ₜ[ℂ] ket {1}) (vacuum D ⊗ₜ[ℂ] ket {1}) = 1 := by
  rw [pairing_down, sourcePairing_vacuum]

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeChargeForm
