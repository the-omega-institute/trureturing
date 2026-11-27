/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldCriticalMatter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldCriticalMatter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Critical matter on the literal Leech orbifold tensored with the hyperbolic lattice. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMatter

/-! The hyperbolic lattice contributes the two additional bosonic directions
through its own lattice field on its own carrier. -/

set_option autoImplicit false
noncomputable section
open scoped TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldCriticalMatter

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
open ActualLeechOrbifoldMatter (Orbifold)
open VirasoroBRST (MatterDatum)

/-- The standalone even lattice with Gram matrix U. -/
def hyperbolicPlane : LatticeData where
  rank := 2
  G := OrderedHyperbolicExtension.U
  symmetric := OrderedHyperbolicExtension.U_symmetric
  even_diagonal i := by simp

private theorem plane_inverse :
    gramComplex hyperbolicPlane * gramComplex hyperbolicPlane = 1 := by
  let castMatrix : Matrix (Fin 2) (Fin 2) ℤ →+* Matrix (Fin 2) (Fin 2) ℂ :=
    (Int.castRingHom ℂ).mapMatrix
  change castMatrix OrderedHyperbolicExtension.U * castMatrix OrderedHyperbolicExtension.U = 1
  rw [← map_mul, OrderedHyperbolicExtension.U_mul_U, map_one]

/-- The actual hyperbolic lattice field provides charge two and statewise
truncation on the indefinite lattice. -/
@[instance_reducible] def hyperbolicMatter : MatterDatum (Carrier hyperbolicPlane) where
  mode := sugawaraMode hyperbolicPlane (gramComplex hyperbolicPlane)
  centralCharge := 2
  virasoro m n := by
    simpa only [show hyperbolicPlane.rank = 2 from rfl, Nat.cast_ofNat] using
      sugawaraMode_virasoro hyperbolicPlane _ plane_inverse plane_inverse m n
  positive_mode_truncation x := by
    let A := sugawaraField hyperbolicPlane (gramComplex hyperbolicPlane)
    let e := ((HahnModule.of ℂ).symm (A x)).order
    refine ⟨-e, fun n hn => ?_⟩
    exact VertexOperator.ncoeff_eq_zero_of_lt_order A (n+1) x
      (show -(n+1)-1 < e by omega)

section Tensor

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable (A : MatterDatum V) (B : MatterDatum W)

private def tensorMode (n : ℤ) : Module.End ℂ (V ⊗[ℂ] W) :=
  (A.mode n).rTensor W + (B.mode n).lTensor V

private theorem tensor_virasoro (m n : ℤ) :
    tensorMode A B m * tensorMode A B n - tensorMode A B n * tensorMode A B m =
      ((m-n : ℤ) : ℂ) • tensorMode A B (m+n) +
        (if m+n = 0 then ((A.centralCharge+B.centralCharge) / 12) *
          ((m : ℂ)^3-m) else 0) • 1 := by
  let F := fun k => (A.mode k).rTensor W
  let G := fun k => (B.mode k).lTensor V
  let z := fun c : ℂ => if m+n = 0 then (c / 12) * ((m : ℂ)^3-m) else 0
  have left : F m * F n - F n * F m =
      ((m-n : ℤ) : ℂ) • F (m+n) + z A.centralCharge • 1 := by
    let lift := Module.End.rTensorAlgHom ℂ V W
    have h := congrArg lift (A.virasoro m n)
    have lift_mode (k : ℤ) : lift (A.mode k) = F k := rfl
    simpa only [map_mul, map_sub, map_add, map_smul, map_one, lift_mode] using h
  have right : G m * G n - G n * G m =
      ((m-n : ℤ) : ℂ) • G (m+n) + z B.centralCharge • 1 := by
    let lift := Module.End.lTensorAlgHom ℂ W V
    have h := congrArg lift (B.virasoro m n)
    have lift_mode (k : ℤ) : lift (B.mode k) = G k := rfl
    simpa only [map_mul, map_sub, map_add, map_smul, map_one, lift_mode] using h
  have cross (i j : ℤ) : F i * G j = G j * F i := by
    change ((A.mode i).rTensor W).comp ((B.mode j).lTensor V) =
      ((B.mode j).lTensor V).comp ((A.mode i).rTensor W)
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have central : z A.centralCharge + z B.centralCharge =
      z (A.centralCharge + B.centralCharge) := by
    dsimp only [z]
    split_ifs <;> ring
  change (F m + G m) * (F n + G n) - (F n + G n) * (F m + G m) =
    ((m-n : ℤ) : ℂ) • (F (m+n) + G (m+n)) + z (A.centralCharge + B.centralCharge) • 1
  calc
    _ = (F m * F n - F n * F m) + (G m * G n - G n * G m) +
          (F m * G n - G n * F m) + (G m * F n - F n * G m) := by noncomm_ring
    _ = _ := by
      rw [cross m n, cross n m, sub_self, sub_self, add_zero, add_zero, left, right,
        add_add_add_comm, ← smul_add, ← add_smul, central]

private theorem tensor_truncation (x : V ⊗[ℂ] W) :
    ∃ K : ℤ, ∀ n : ℤ, K < n → tensorMode A B n x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    obtain ⟨I, hI⟩ := A.positive_mode_truncation v
    obtain ⟨J, hJ⟩ := B.positive_mode_truncation w
    refine ⟨max I J, fun n hn => ?_⟩
    simp [tensorMode, hI n ((le_max_left I J).trans_lt hn),
      hJ n ((le_max_right I J).trans_lt hn)]
  | add x y hx hy =>
    obtain ⟨I, hI⟩ := hx
    obtain ⟨J, hJ⟩ := hy
    exact ⟨max I J, fun n hn => by
      rw [map_add, hI n ((le_max_left I J).trans_lt hn),
        hJ n ((le_max_right I J).trans_lt hn), add_zero]⟩

end Tensor

/-- The actual orbifold matter tensored with the standalone hyperbolic lattice. -/
abbrev Matter := Orbifold ⊗[ℂ] Carrier hyperbolicPlane

/-- The two genuine matter actions give a critical, statewise truncated
Virasoro datum on the orbifold tensor lattice. -/
@[instance_reducible] def matter : MatterDatum Matter where
  mode := tensorMode ActualLeechOrbifoldMatter.matter hyperbolicMatter
  centralCharge := 26
  virasoro m n := by
    have h := tensor_virasoro ActualLeechOrbifoldMatter.matter hyperbolicMatter m n
    have hc : ActualLeechOrbifoldMatter.matter.centralCharge + hyperbolicMatter.centralCharge =
        (26 : ℂ) := by
      change (24 : ℂ) + 2 = 26
      norm_num
    rwa [hc] at h
  positive_mode_truncation := tensor_truncation ActualLeechOrbifoldMatter.matter hyperbolicMatter

#print axioms hyperbolicMatter
#print axioms matter

end D5.S3.VertexAlgebra.ActualLeechOrbifoldCriticalMatter
