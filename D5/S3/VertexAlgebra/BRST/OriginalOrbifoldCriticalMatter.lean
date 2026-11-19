/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldCriticalMatter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldCriticalMatter
   mirror-E: none(waiver:algebraic-virasoro-brst-anomaly)
   anchors: []
   utility: none
   digest: Critical BRST matter from the original Leech sign orbifold and hyperbolic plane. -/

import D5.S3.VertexAlgebra.BRST.VirasoroBRST
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic
import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldConformal

/-! The original Leech orbifold tensored with the even hyperbolic lattice sector. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldCriticalMatter

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeGeneratingFieldLocality (LatticeData)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open TwistedGround
open D5.S3.Quantum.Fermionic

local notation "ghostVacuum" => CountableOccupationFock.vacuum

private def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric i := Fin.elim0 i
  even_diagonal i := Fin.elim0 i

/-- The ordered integral hyperbolic extension of the rank-zero lattice. -/
abbrev hyperbolicData : LatticeData := OrderedHyperbolicExtension.extend zeroLattice

theorem hyperbolic_gram : hyperbolicData.G = OrderedHyperbolicExtension.U := by
  have hnew (i : Fin 2) : OrderedHyperbolicExtension.new zeroLattice i = i := by
    apply Fin.ext
    exact Nat.zero_add i.val
  ext i j
  simpa only [hnew] using OrderedHyperbolicExtension.gram_new_new zeroLattice i j

/-- In the ordered null basis the complex inverse has the same off-diagonal entries. -/
def hyperbolicInverse : Matrix (Fin hyperbolicData.rank) (Fin hyperbolicData.rank) ℂ :=
  OrderedHyperbolicExtension.U.map (Int.castRingHom ℂ)

private theorem gramComplex_eq_inverse : gramComplex hyperbolicData = hyperbolicInverse :=
  congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom ℂ)) hyperbolic_gram

theorem hyperbolic_inverse_left : hyperbolicInverse * gramComplex hyperbolicData = 1 := by
  rw [gramComplex_eq_inverse, hyperbolicInverse, ← Matrix.map_mul,
    OrderedHyperbolicExtension.U_mul_U]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem hyperbolic_inverse_right : gramComplex hyperbolicData * hyperbolicInverse = 1 := by
  rw [gramComplex_eq_inverse]
  simpa only [gramComplex_eq_inverse] using hyperbolic_inverse_left

/-- The original fixed and negative twisted sectors of the actual Leech lattice. -/
abbrev Orbifold :=
  TwistedGround.OriginalOrbifoldField.Carrier leechData leech_spec.2.1

/-- All integral hyperbolic charges with their polynomial oscillators. -/
abbrev Hyperbolic := LatticeGeneratingFieldLocality.Carrier hyperbolicData

abbrev Matter := Orbifold ⊗[ℂ] Hyperbolic

def orbifoldMode (n : ℤ) : Module.End ℂ Orbifold :=
  OriginalOrbifoldConformal.L leechData leech_spec.2.1 leech_spec.2.2.1 n

def orbifoldVertexAlgebra : LatticeActualVertexAlgebra.StateFieldVertexAlgebra Orbifold :=
  OriginalOrbifoldVertexAlgebra.originalVertexAlgebra leechData leech_spec.2.1
    leech_spec.2.2.1 leech_spec.1

theorem orbifoldMode_eq_stateField (n : ℤ) :
    orbifoldMode n =
      (orbifoldVertexAlgebra.stateField
        (OriginalOrbifoldConformal.conformalVector leechData leech_spec.2.1))[[n + 1]] :=
  OriginalOrbifoldConformal.L_eq_mode leechData leech_spec.2.1 leech_spec.2.2.1 leech_spec.1 n

def hyperbolicMode (n : ℤ) : Module.End ℂ Hyperbolic :=
  sugawaraMode hyperbolicData hyperbolicInverse n

private theorem hyperbolicMode_eq_stateField (n : ℤ) :
    hyperbolicMode n =
      (LatticeAllStateField.Y hyperbolicData
        (LatticeActualConformalState.omega hyperbolicData hyperbolicInverse))[[n + 1]] :=
  (LatticeActualConformalState.omega_modes hyperbolicData hyperbolicInverse n).symm

/-- The two actual Virasoro actions on the algebraic tensor product. -/
def mode (n : ℤ) : Module.End ℂ Matter :=
  (orbifoldMode n).rTensor Hyperbolic + (hyperbolicMode n).lTensor Orbifold

theorem mode_minus_one_eq_translation :
    mode (-1) = orbifoldVertexAlgebra.translation.rTensor Hyperbolic +
      (LatticeSugawaraConformal.translation hyperbolicData).lTensor Orbifold := by
  have hO : orbifoldMode (-1) = orbifoldVertexAlgebra.translation :=
    OriginalOrbifoldConformal.L_minus_one_eq_translation leechData leech_spec.2.1
      leech_spec.2.2.1 leech_spec.1
  have hH : hyperbolicMode (-1) = LatticeSugawaraConformal.translation hyperbolicData :=
    LatticeSugawaraConformal.sugawaraMode_minus_one_eq_translation hyperbolicData
      hyperbolicInverse hyperbolic_inverse_left hyperbolic_inverse_right
  exact congrArg₂ (fun T S => T.rTensor Hyperbolic + S.lTensor Orbifold) hO hH

private theorem tensor_commutator (m n : ℤ) :
    mode m * mode n - mode n * mode m =
      (orbifoldMode m * orbifoldMode n - orbifoldMode n * orbifoldMode m).rTensor Hyperbolic +
      (hyperbolicMode m * hyperbolicMode n - hyperbolicMode n * hyperbolicMode m).lTensor
        Orbifold := by
  apply TensorProduct.ext'
  intro v w
  simp only [mode, LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    map_add, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.sub_tmul,
    TensorProduct.tmul_sub]
  abel

theorem mode_virasoro (m n : ℤ) :
    mode m * mode n - mode n * mode m =
      ((m - n : ℤ) : ℂ) • mode (m + n) +
        (if m + n = 0 then (26 : ℂ) / 12 * ((m : ℂ)^3 - m) else 0) • 1 := by
  have hO :
      orbifoldMode m * orbifoldMode n - orbifoldMode n * orbifoldMode m =
        ((m - n : ℤ) : ℂ) • orbifoldMode (m + n) +
          (if m + n = 0 then (24 : ℂ) / 12 * ((m : ℂ)^3 - m) else 0) • 1 :=
    OriginalOrbifoldConformal.L_virasoro leechData leech_spec.2.1 leech_spec.2.2.1
      leech_spec.1 m n
  have hH :
      hyperbolicMode m * hyperbolicMode n - hyperbolicMode n * hyperbolicMode m =
        ((m - n : ℤ) : ℂ) • hyperbolicMode (m + n) +
          (if m + n = 0 then (2 : ℂ) / 12 * ((m : ℂ)^3 - m) else 0) • 1 := by
    have hRank : (hyperbolicData.rank : ℂ) = 2 := by
      change ((2 : ℕ) : ℂ) = 2
      norm_num
    rw [← hRank]
    exact LatticeSugawaraVirasoro.sugawaraMode_virasoro hyperbolicData hyperbolicInverse
      hyperbolic_inverse_left hyperbolic_inverse_right m n
  have hIdO : (1 : Module.End ℂ Orbifold).rTensor Hyperbolic = (1 : Module.End ℂ Matter) :=
    LinearMap.rTensor_id Hyperbolic Orbifold
  have hIdH : (1 : Module.End ℂ Hyperbolic).lTensor Orbifold = (1 : Module.End ℂ Matter) :=
    LinearMap.lTensor_id Orbifold Hyperbolic
  have hCentral :
      (if m + n = 0 then (24 : ℂ) / 12 * ((m : ℂ)^3 - m) else 0) +
        (if m + n = 0 then (2 : ℂ) / 12 * ((m : ℂ)^3 - m) else 0) =
        (if m + n = 0 then (26 : ℂ) / 12 * ((m : ℂ)^3 - m) else 0) := by
    split_ifs <;> ring
  rw [tensor_commutator, hO, hH]
  simp only [mode, LinearMap.rTensor_add, LinearMap.lTensor_add, LinearMap.rTensor_smul,
    LinearMap.lTensor_smul, hIdO, hIdH, smul_add]
  rw [add_add_add_comm, ← add_smul, hCentral]

private theorem field_mode_truncation {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : VertexOperator ℂ V) (v : V) :
    ∃ B : ℤ, ∀ n : ℤ, B < n → (F[[n + 1]]) v = 0 := by
  refine ⟨-((HahnModule.of ℂ).symm (F v)).order - 2, ?_⟩
  intro n hn
  exact VertexOperator.ncoeff_eq_zero_of_lt_order F (n + 1) v (by omega)

/-- A statewise bound for every algebraic tensor, including finite sums of pure tensors. -/
theorem positive_mode_truncation (x : Matter) :
    ∃ B : ℤ, ∀ n : ℤ, B < n → mode n x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
      obtain ⟨B, hB⟩ := field_mode_truncation
        (orbifoldVertexAlgebra.stateField
          (OriginalOrbifoldConformal.conformalVector leechData leech_spec.2.1)) v
      obtain ⟨C, hC⟩ := field_mode_truncation (LatticeAllStateField.Y hyperbolicData
        (LatticeActualConformalState.omega hyperbolicData hyperbolicInverse)) w
      refine ⟨max B C, fun n hn => ?_⟩
      simp only [mode, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        orbifoldMode_eq_stateField, hyperbolicMode_eq_stateField,
        hB n ((le_max_left B C).trans_lt hn), hC n ((le_max_right B C).trans_lt hn),
        TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]
  | add x y hx hy =>
      obtain ⟨B, hB⟩ := hx
      obtain ⟨C, hC⟩ := hy
      refine ⟨max B C, fun n hn => ?_⟩
      rw [map_add, hB n ((le_max_left B C).trans_lt hn),
        hC n ((le_max_right B C).trans_lt hn), add_zero]

@[instance_reducible] def matterDatum : VirasoroBRST.MatterDatum Matter where
  mode := mode
  centralCharge := 26
  virasoro := mode_virasoro
  positive_mode_truncation := positive_mode_truncation

abbrev State := VirasoroBRST.State Matter

/-- The native statewise finite BRST charge on the original matter and bc carrier. -/
abbrev Q : Module.End ℂ State := VirasoroBRST.Q matterDatum

abbrev b (r : ℤ) : Module.End ℂ State := VirasoroBRST.ghostB matterDatum r

theorem Q_squared : Q ^ 2 = 0 := by
  rw [VirasoroBRST.square_anomaly matterDatum]
  change (((26 : ℂ) - 26) / 26) • VirasoroBRST.ghostSquareAnomaly matterDatum = 0
  rw [sub_self, zero_div, zero_smul]

/-- The b Ward identity holds on the entire matter-ghost carrier for every integer mode. -/
theorem Q_ward_b (r : ℤ) :
    Q * b r + b r * Q =
      TensorProduct.map (mode r) LinearMap.id +
        TensorProduct.map LinearMap.id (BcGhostVirasoro.L r) :=
  VirasoroBRST.Q_ward_b matterDatum r

def matterVacuum : Matter :=
  orbifoldVertexAlgebra.vacuum ⊗ₜ[ℂ] LatticeAllStateField.vacuum hyperbolicData

def vacuum : State := matterVacuum ⊗ₜ[ℂ] ghostVacuum

private theorem mode_matterVacuum (n : ℤ) (hn : -1 ≤ n) : mode n matterVacuum = 0 := by
  rcases eq_or_lt_of_le hn with h | h
  · subst n
    rw [mode_minus_one_eq_translation]
    simp only [matterVacuum, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      orbifoldVertexAlgebra.translation_vacuum, LatticeAllStateField.vacuum,
      LatticeSugawaraConformal.translation_vacuum, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero, add_zero]
  · have hO : orbifoldMode n orbifoldVertexAlgebra.vacuum = 0 := by
      rw [orbifoldMode_eq_stateField]
      exact orbifoldVertexAlgebra.creativity _ (n + 1) (by omega)
    have hH : hyperbolicMode n (LatticeAllStateField.vacuum hyperbolicData) = 0 := by
      rw [hyperbolicMode_eq_stateField]
      exact LatticeAllStateField.stateField_creativity _ _ (n + 1) (by omega)
    simp only [mode, matterVacuum, LinearMap.add_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul, hO, hH, TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]

/-- The tensor of the original orbifold, lattice, and SL₂ ghost vacua is BRST closed. -/
theorem vacuum_closed : Q vacuum = 0 := by
  have hterm (n : ℤ) : VirasoroBRST.summand matterDatum n vacuum = 0 := by
    change TensorProduct.map (mode n) (BcGhostFock.c (-n))
      (matterVacuum ⊗ₜ[ℂ] ghostVacuum) = 0
    rw [TensorProduct.map_tmul]
    by_cases hn : -1 ≤ n
    · rw [mode_matterVacuum n hn, TensorProduct.zero_tmul]
    · rw [BcGhostFock.ghost_vacuum.2.1 (-n) (by omega), TensorProduct.tmul_zero]
  have ht : VirasoroBRST.T matterDatum vacuum = 0 := finsum_eq_zero_of_forall_eq_zero hterm
  change VirasoroBRST.T matterDatum vacuum +
    TensorProduct.map LinearMap.id BcGhostBRST.Qg (matterVacuum ⊗ₜ[ℂ] ghostVacuum) = 0
  rw [ht, TensorProduct.map_tmul, BcGhostBRST.Qg_vacuum, TensorProduct.tmul_zero, add_zero]

#print axioms hyperbolic_gram
#print axioms hyperbolic_inverse_left
#print axioms hyperbolic_inverse_right
#print axioms orbifoldMode_eq_stateField
#print axioms mode_minus_one_eq_translation
#print axioms mode_virasoro
#print axioms positive_mode_truncation
#print axioms matterDatum
#print axioms Q_squared
#print axioms Q_ward_b
#print axioms vacuum_closed

end D5.S3.VertexAlgebra.OriginalOrbifoldCriticalMatter
