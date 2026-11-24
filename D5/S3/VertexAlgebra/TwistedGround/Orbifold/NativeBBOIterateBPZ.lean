import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOProductBPZ
import D5.S3.VertexAlgebra.StateField.SkewSymmetry

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOProductBPZ

open ActualLeechHyperbolic (leechData leech_spec)
open NativeOddTwistedIntertwiner (leechUnit oddMode)
open NativeOddUpperRightSkew (rightField lowering)
open NativeMixedPairField (mu)
open Complex (I)
open private oddGradeProjection oddGradeInclusion sum_oddGradeProjections from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairState
open NativeFixedPairField (nu nu_coeff_of_grade)
open NativeFixedPairState (fixedPairState fixedPairState_grade fixedPairState_pairing
  fixedPairWeight fixedPairing fixedPairing_apply)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open SourceBPZ.AllStateTranspose (sourcePairing_allState)
open OriginalSkewAdjoints (sourcePairing_translation)
open LatticeAllStateField (Y)
open LatticeGeneratingFieldLocality LatticeInvolution LatticePositiveEnergy
open LatticeHalfFockGradedTrace (actualGrade)
open LatticeSugawaraCurrents (gramComplex)
open LatticeHalfFockFiniteCorrection (sourceWeight)
open MvPolynomial
open private sourceL1 from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalSkewAdjoints
open private oddMode_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

local notation "ℒ" => leechData
local notation "P" => sourcePairing ℒ
local notation "S" => LatticeSugawaraConformal.translation ℒ
local notation "V" => sourceL1 ℒ

/-- The actual untwisted odd/odd source mode takes values in the original fixed carrier. -/
def oddOddMode (o d : Odd) (n : ℤ) : FixedCarrier ℒ :=
  ⟨((Y ℒ o.val)[[n]]) d.val, by
    apply (mem_fixedSpace ℒ _).mpr
    have h := mode_eigenvalue_selection ℒ (-1) (-1) o.val d.val
      ((mem_eigenspace ℒ (-1) _).mp o.property)
      ((mem_eigenspace ℒ (-1) _).mp d.property) n
    simpa using h⟩

private theorem translation_pairing (j : ℕ) (a d : Carrier ℒ) :
    P ((S ^ j) a) d = P a ((V ^ j) d) := by
  induction j generalizing d with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ' S, Module.End.mul_apply, sourcePairing_translation ℒ leechUnit,
      ih, pow_succ V, Module.End.mul_apply]

private theorem negative_source_grade (E : ℤ) (a : Carrier ℒ)
    (ha : a ∈ grade ℒ E) (hE : E < 0) : a = 0 := by
  apply (carrierCoeffEquiv ℒ).injective
  ext x
  simp only [map_zero, Finsupp.zero_apply]
  change (a x.1).coeff x.2 = 0
  apply (mem_grade_iff ℒ E a).mp ha x
  have h := chargeEnergy_nonneg ℒ leech_spec.2.2.1 x.1
  dsimp [energy]
  omega

/-- The exact positive-energy cutoff for the source BPZ sum. -/
def sourceSupportBound (o : Odd) : ℕ :=
  o.val.support.sup (fun α => weightedTotalDegree (sourceWeight ℒ) (o.val α))

/-- Source skew followed by source BPZ. The detector of the fixed pair is
an actual odd/odd lattice product of lowered odd states. -/
theorem fixed_odd_mode_pairing (A O n : ℤ) (a : FixedCarrier ℒ) (o d : Odd)
    (ha : a.val ∈ grade ℒ A) (ho : o.val ∈ grade ℒ O) :
    P (oddMode ℒ a n o).val d.val =
      ∑ j ∈ Finset.range (A+O-n).toNat,
        ((-1 : ℂ)^(n+(j : ℤ)+1) / (j.factorial : ℂ)) *
          ((-1 : ℂ)^O * ∑ h ∈ Finset.range (sourceSupportBound o+1),
            (h.factorial : ℂ)⁻¹ * P a.val
              (oddOddMode (oddLower o h) (oddLower d j) (2*O-(h : ℤ)-n-(j : ℤ)-2)).val) := by
  classical
  let f (j : ℕ) := (((-1 : ℂ)^(n+(j : ℤ)+1)) / (j.factorial : ℂ)) •
    (S ^ j) (((Y ℒ o.val)[[n+(j : ℤ)]]) a.val)
  have hs := ((StateField.SkewSymmetry.skew_symmetry
    (LatticeActualVertexAlgebra.actualVertexAlgebra ℒ) a.val o.val).1 n)
  have hskew : (oddMode ℒ a n o).val = ∑ᶠ j, f j := hs.2
  have hfin : Function.support f ⊆ (Finset.range (A+O-n).toNat : Set ℕ) := by
    intro j hj
    by_contra hout
    have hj' : (A+O-n).toNat ≤ j := Nat.le_of_not_gt (fun h => hout (Finset.mem_range.mpr h))
    have hgrade := positive_actual_mode_grade ℒ leech_spec.2.2.1 O A (n+(j : ℤ))
      o.val a.val ho ha
    have hzero := negative_source_grade _ _ hgrade (by omega)
    exact hj (by simp [f, hzero])
  rw [hskew, finsum_eq_sum_of_support_subset f hfin]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [f, map_smul, LinearMap.smul_apply, smul_eq_mul, translation_pairing]
  congr 1
  have hbpz := sourcePairing_allState ℒ leechUnit O (n+(j : ℤ)) o.val ho a.val ((V ^ j) d.val)
  rw [hbpz]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  change _ * P a.val (((Y ℒ ((V ^ h) o.val))[[2*O-(h : ℤ)-(n+(j : ℤ))-2]]) ((V ^ j) d.val)) = _
  rw [show 2*O-(h : ℤ)-(n+(j : ℤ))-2 = 2*O-(h : ℤ)-n-(j : ℤ)-2 by ring]
  rfl

/-- Actual BBO iterate in terms of fixed-pair BPZ applied to actual O,O
products, each carrying the complete source adjoint and skew factors. -/
theorem bbo_iterate_modes (M K : ℕ) (r n O : ℤ) (b c : State true) (o d : Odd)
    (hb : b.val ∈ actualGrade ℒ leechUnit M) (hc : c.val ∈ actualGrade ℒ leechUnit K)
    (ho : o.val ∈ grade ℒ O) :
    P (oddMode ℒ ((nu true b).coeff (-2*r-2) c) n o).val d.val =
      ∑ j ∈ Finset.range (fixedPairWeight M K r+O-n).toNat,
        ((-1 : ℂ)^(n+(j : ℤ)+1) / (j.factorial : ℂ)) *
          ((-1 : ℂ)^O * ∑ h ∈ Finset.range (sourceSupportBound o+1),
            (h.factorial : ℂ)⁻¹ * fixedPairing true M K r b c
              (oddOddMode (oddLower o h) (oddLower d j) (2*O-(h : ℤ)-n-(j : ℤ)-2))) := by
  rw [nu_coeff_of_grade true M K r b c hb hc,
    fixed_odd_mode_pairing (fixedPairWeight M K r) O n _ o d (fixedPairState_grade true M K r b c) ho]
  simp only [fixedPairState_pairing true M K r b c hb hc]


/-- A homogeneous component of any original odd source, with its actual grade. -/
def oddComponent (h : ℤ) (a : Odd) : Odd :=
  oddGradeInclusion h (oddGradeProjection h a)

theorem oddComponent_grade (h : ℤ) (a : Odd) :
    (oddComponent h a).val ∈ grade ℒ h :=
  (oddGradeProjection h a).property.1

/-- Use the finite grade supports to allow completely arbitrary odd sources
and detectors in the direct product formula. -/
theorem bbo_product_all_detectors (M K : ℕ) (k l : ℤ)
    (b c : State true) (o d : Odd)
    (hb : b.val ∈ actualGrade ℒ leechUnit M)
    (hc : c.val ∈ actualGrade ℒ leechUnit K) :
    P ((mu true b).coeff (-2*k-3) ((rightField ℒ leechUnit true c).coeff (-2*l-3) o)).val d.val =
      ∑ O ∈ stateEnergies ℒ o.val, ∑ D ∈ stateEnergies ℒ d.val,
        I ^ (-(3+(M : ℤ))) * ∑ j ∈ Finset.range (M/2+1),
          (j.factorial : ℂ)⁻¹ * ∑ p ∈ Finset.range (((M : ℤ)+2*D-2*((M : ℤ)-k)-3)/2+1).toNat,
            ∑ q ∈ Finset.range (((K : ℤ)+2*O-2*l-3)/2+1).toNat,
              (I ^ (-2*((M : ℤ)-k-(j : ℤ)+(p : ℤ))-3) * (p.factorial : ℂ)⁻¹) *
                (I ^ (-2*(l+(q : ℤ))-3) * (q.factorial : ℂ)⁻¹) *
                modeComposition D O ((M : ℤ)-k-(j : ℤ)+(p : ℤ)) (l+(q : ℤ)) p q
                  ((leechData.rank : ℂ)/16 +
                    (((M : ℤ)+2*D-2*((M : ℤ)-k)-3-2*(p : ℤ) : ℤ) : ℂ)/2)
                  ((lowering ℒ leechUnit true ^ j) b) c (oddComponent O o) (oddComponent D d) := by
  classical
  let F₀ := (rightField ℒ leechUnit true c).coeff (-2*l-3)
  let G₀ := (mu true b).coeff (-2*k-3)
  have hs (x : Odd) : (∑ h ∈ stateEnergies ℒ x.val, oddComponent h x) = x :=
    sum_oddGradeProjections x
  change P (G₀ (F₀ o)).val d.val = _
  calc
    _ = P (G₀ (F₀ (∑ O ∈ stateEnergies ℒ o.val, oddComponent O o))).val
        ((∑ D ∈ stateEnergies ℒ d.val, oddComponent D d) : Odd).val := by rw [hs o, hs d]
    _ = ∑ O ∈ stateEnergies ℒ o.val, ∑ D ∈ stateEnergies ℒ d.val,
        P (G₀ (F₀ (oddComponent O o))).val (oddComponent D d).val := by
      simp only [map_sum, Submodule.coe_sum, LinearMap.sum_apply]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro O _
      apply Finset.sum_congr rfl
      intro D _
      exact bbo_product_modes M K k l D O b c (oddComponent O o) (oddComponent D d) hb hc
        (oddComponent_grade O o) (oddComponent_grade D d)

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOProductBPZ
