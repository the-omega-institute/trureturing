/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetFieldSeparation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetFieldSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-state native fields commute with transverse multiplication by the Schur shift. -/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetSeparation

/-! Native normal-product recursion extends the transverse substitution from
charged ground fields to every original source state. The target remains an
arbitrary ambient state. The construction and conventions are those of
Bakalov--Kac, math/0402315v1, section 4.1, and the native imported residue
operations retain their Carnahan Apache-2.0 attribution. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetFieldSeparation

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeSugawaraCurrents FieldNormalProduct
open LatticeCosetCompression LatticeCosetTransverse LatticeCosetSeparation
open LatticeDiscriminantTheta MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

open private current_transverse_mul from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetSeparation
open private injection_single from D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression
open private multiplication_recursion from D5.S3.VertexAlgebra.Sectors.LatticeDualCosetModule
open private derivative_modes from D5.S3.VertexAlgebra.LatticeAllStateField

private theorem map_finsum_linear {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (L : V →ₗ[ℂ] W) (f : ℕ → V)
    (hf : Function.HasFiniteSupport f) :
    L (∑ᶠ i, f i) = ∑ᶠ i, L (f i) := L.toAddMonoidHom.map_finsum hf

private theorem high_modes_finite {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (A : VertexOperator ℂ V) (F : ℕ → V →ₗ[ℂ] W) (m : ℤ) (v : V) :
    Function.HasFiniteSupport (fun j : ℕ => F j (((A)[[m+j]]) v)) := by
  classical
  let N : ℕ := (-((HahnModule.of ℂ).symm (A v)).order-m).toNat
  apply (Finset.finite_toSet (Finset.range N)).subset
  intro j hj
  apply Finset.mem_range.mpr
  by_contra hn
  have hz : ((A)[[m+j]]) v = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    have : N ≤ j := by omega
    dsimp only [N] at this
    omega
  exact hj (by dsimp only; rw [hz, map_zero])

private theorem normal_commutator {V : Type} [AddCommGroup V] [Module ℂ V]
    (A F : VertexOperator ℂ V) (M : Module.End ℂ V) (s : ℂ) (r : ℤ)
    (hA : ∀ m v, ((A)[[m]]) (M v) = M (((A)[[m]]) v))
    (hF : ∀ m v, ((F)[[m]]) (M v) = M (((F)[[m]]) v) - s • (((F)[[m-r]]) v))
    (m : ℤ) (v : V) :
    (((normalMinusOne A F).1)[[m]]) (M v) =
      M ((((normalMinusOne A F).1)[[m]]) v) -
        s • ((((normalMinusOne A F).1)[[m-r]]) v) := by
  have h₁ := high_modes_finite F (fun j => ((A)[[-(j : ℤ)-1]])) m v
  have h₁r := high_modes_finite F (fun j => ((A)[[-(j : ℤ)-1]])) (m-r) v
  have h₂ := high_modes_finite A (fun j => ((F)[[m-j-1]])) 0 v
  have h₂r := high_modes_finite A (fun j => ((F)[[m-r-j-1]])) 0 v
  simp only [zero_add] at h₂ h₂r
  have left (j : ℕ) :
      ((A)[[-(j : ℤ)-1]]) (((F)[[m+j]]) (M v)) =
        M (((A)[[-(j : ℤ)-1]]) (((F)[[m+j]]) v)) -
          s • (((A)[[-(j : ℤ)-1]]) (((F)[[m-r+j]]) v)) := by
    rw [hF, map_sub, map_smul, hA]
    rw [show m+(j : ℤ)-r = m-r+j by omega]
  have right (j : ℕ) :
      ((F)[[m-j-1]]) (((A)[[j]]) (M v)) =
        M (((F)[[m-j-1]]) (((A)[[j]]) v)) -
          s • (((F)[[m-r-j-1]]) (((A)[[j]]) v)) := by
    rw [hA, hF]
    rw [show m-(j : ℤ)-1-r = m-r-j-1 by omega]
  rw [(normalMinusOne A F).2, (normalMinusOne A F).2,
    (normalMinusOne A F).2]
  simp_rw [left, right]
  have hs₁ : Function.HasFiniteSupport (fun j : ℕ =>
      s • (((A)[[-(j : ℤ)-1]]) (((F)[[m-r+j]]) v))) :=
    h₁r.fun_comp (smul_zero s)
  have hs₂ : Function.HasFiniteSupport (fun j : ℕ =>
      s • (((F)[[m-r-j-1]]) (((A)[[j]]) v))) :=
    h₂r.fun_comp (smul_zero s)
  have mapSum (f : ℕ → V) (hf : Function.HasFiniteSupport f) :
      M (∑ᶠ j, f j) = ∑ᶠ j, M (f j) := M.toAddMonoidHom.map_finsum hf
  rw [finsum_sub_distrib (h₁.fun_comp M.map_zero)
      hs₁,
    finsum_sub_distrib (h₂.fun_comp M.map_zero) hs₂,
    ← mapSum _ h₁, ← mapSum _ h₂,
    ← smul_finsum' s h₁r, ← smul_finsum' s h₂r]
  simp only [map_add, smul_add]
  abel

variable (D : LatticeData) {e : ℕ}
variable (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

/-- Every descendant source has the same transverse contraction. This is an
identity on the full native ambient carrier, before any projection. -/
theorem field_transverse_commutator (hD : (gramReal D).PosDef)
    (a : Fin e → ℤ) (u : Carrier D) (j : Fin e) (k : ℕ) (m : ℤ)
    (v : Carrier (ambient D e B C hC hCe)) :
    ((Y (ambient D e B C hC hCe) (injection D B C hC hCe a u))[[m]])
        (multiply _ (transverse D B C hC hCe j k) v) =
      multiply _ (transverse D B C hC hCe j k)
        (((Y (ambient D e B C hC hCe) (injection D B C hC hCe a u))[[m]]) v) -
      (transversePair D B C a j : ℂ) •
        (((Y (ambient D e B C hC hCe) (injection D B C hC hCe a u))
          [[m-(k+1 : ℕ)]]) v) := by
  induction u using Finsupp.induction_linear generalizing m v with
  | zero => simp
  | add u w hu hw =>
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, hu, hw, smul_add]
    abel
  | single n f =>
    induction f using MvPolynomial.induction_on generalizing m v with
    | C z =>
      have hz : MvPolynomial.C z = z • (1 : Oscillator D) := by
        simp [MvPolynomial.smul_eq_C_mul]
      rw [hz, ← Finsupp.smul_single]
      simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply]
      rw [injection_single, map_one, stateField_ground,
        ground_transverse_commutator D B C hC hCe hD]
      simp only [map_smul, smul_sub, smul_smul]
      simp [mul_comm]
    | add f g hf hg =>
      simp only [Finsupp.single_add, map_add, Pi.add_apply, LinearMap.add_apply,
        hf, hg, smul_add]
      abel
    | mul_X f x hf =>
      have hrec : Y (ambient D e B C hC hCe)
          (injection D B C hC hCe a (Finsupp.single n (f * X x))) =
          (normalMinusOne
            (dividedDerivative x.2 (neutralField (ambient D e B C hC hCe) (x.1.castAdd e)))
            (Y (ambient D e B C hC hCe)
              (injection D B C hC hCe a (Finsupp.single n f)))).1 := by
        have hx : polynomialInjection D B C hC hCe (X x) =
            X (x.1.castAdd e, x.2) := by simp [polynomialInjection]
        simp only [injection_single]
        rw [map_mul, hx, mul_comm]
        rw [injection_single D B C hC hCe a n f]
        exact multiplication_recursion (ambient D e B C hC hCe)
          (x.1.castAdd e, x.2) (liftCharge D B C hC hCe a n)
          (polynomialInjection D B C hC hCe f)
      rw [hrec]
      apply normal_commutator
      · intro t w
        rw [derivative_modes (ambient D e B C hC hCe) (x.1.castAdd e, x.2) t]
        simp only [LinearMap.smul_apply,
          current_transverse_mul D B C hC hCe hD, map_smul]
      · exact hf

end
end D5.S3.VertexAlgebra.LatticeCosetFieldSeparation
