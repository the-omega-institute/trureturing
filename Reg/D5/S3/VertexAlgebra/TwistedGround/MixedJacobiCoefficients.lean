import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients
import Batteries.Tactic.OpenPrivate
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace
open LatticeAllStateField LatticePositiveEnergy LatticeInvolution
open _root_.D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open LatticeSugawaraCurrents LatticeSugawaraVirasoro
open HalfFock.LatticeHalfFockParityField
open _root_.D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private T originalL1 from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

namespace mixed_first_input_reindexed_pairing
def arena : Arena where
  signature := complexSignature
  Law observed := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (b : fixedGrade D E) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (j N : ℕ) (hN : ((H : ℤ)+d-r-2).toNat ≤ N),
    observed.readout () ()
      (normalizedCoefficient D hu (m+n-(j : ℤ))
      (((fixedParitySlice D hu (-1)
        (⟨a.val,a.property.2⟩ : FixedCarrier D))[[r+(j : ℤ)]]) u) v E b)
      (∑ p ∈ Finset.range (K-1), ∑ i ∈ Finset.range N,
      ∑ L ∈ Finset.range N, ∑ h ∈ Finset.range N,
        (((-1 : ℂ)^(m+n+r+2-(p : ℤ)-(H : ℤ)-d+(i : ℤ)+(L : ℤ)))/
          ((p.factorial : ℂ)*(i.factorial : ℂ)*(L.factorial : ℂ))) *
        ((-1 : ℂ)^h * Ring.choose
          (2*(d : ℂ)-(r : ℂ)-(L : ℂ)-2-(j : ℂ)) h) *
        actualForm D hu ((T D hu ^ p) v.val)
          ((correctedField D hu b.val).coeff
            (-2*((2*(H : ℤ)-n-r-2+(p : ℤ)-(i : ℤ))+
              (2*d-(L : ℤ)-m-r-2)-((j+h : ℕ) : ℤ))-2)
            ((correctedField D hu ((originalL1 D ^ L) a.val)).coeff
              (-2*(r+((j+h : ℕ) : ℤ))-2) ((T D hu ^ i) u.val))))

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_first_input_reindexed_pairing)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro law
  obtain ⟨D, e, h24, hu, hpos, hpair⟩ :=
    _root_.D5.S3.Arith.Lattices.Golay.RealLeech.exists_positive_even_unimodular_gram
  exact law D hu h24 0 0 0 0 0 0 0 0 0 0 0 (by simp) (by simp) 0 0 (by simp)
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_first_input_reindexed_pairing)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_first_input_reindexed_pairing, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_first_input_reindexed_pairing)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_first_input_reindexed_pairing "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients.mixed_first_input_reindexed_pairing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end mixed_first_input_reindexed_pairing

namespace mixed_source_finite_cancellation
def arena : Arena where
  signature := complexSignature
  Law observed := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (b : fixedGrade D E)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2)
    (u v : ActualTensor D hu) (huH : actualTensorL0 D hu u = (H : ℂ) • u)
    (p q L N : ℕ)
    (hNfirst : ((H : ℤ)+d-r-2).toNat ≤ N)
    (hNsecond : ((K : ℤ)+d-m-2).toNat ≤ N),
    let Q : ℤ := 2*(H : ℤ)-n-r-2+(p : ℤ)-(q : ℤ)
    let R : ℤ := 2*d-(L : ℤ)-m-r-2
    let first (k : ℕ) : ℂ := actualForm D hu ((T D hu ^ p) v)
      ((correctedField D hu ((originalL1 D ^ L) a.val)).coeff (-2*(r+R-(k : ℤ))-2)
        ((correctedField D hu b.val).coeff (-2*(Q+(k : ℤ))-2) ((T D hu ^ q) u)))
    let second (k : ℕ) : ℂ := actualForm D hu ((T D hu ^ p) v)
      ((correctedField D hu b.val).coeff (-2*(Q+R-(k : ℤ))-2)
        ((correctedField D hu ((originalL1 D ^ L) a.val)).coeff
          (-2*(r+(k : ℤ))-2) ((T D hu ^ q) u)))
    observed.readout () ()
      ((∑ᶠ j : ℕ, Ring.choose (r : ℂ) j *
      actualForm D hu ((T D hu ^ p) v)
        ((correctedField D hu
          (((Y D ((originalL1 D ^ L) a.val))[[R+(j : ℤ)]]) b.val)).coeff
            (-2*(r+Q-(j : ℤ))-2) ((T D hu ^ q) u))))
      ((∑ ell ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ h ∈ Finset.range N,
        Ring.choose (L : ℂ) ell * Ring.choose (r : ℂ) j * (-1 : ℂ)^h *
          Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h * first (j+ell+h)) -
      (-1 : ℂ)^R *
        (∑ j ∈ Finset.range N, ∑ h ∈ Finset.range N,
          Ring.choose (m : ℂ) j * (-1 : ℂ)^h *
            Ring.choose (2*(d : ℂ)-(r : ℂ)-(L : ℂ)-2-(j : ℂ)) h * second (j+h)))

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_source_finite_cancellation)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro law
  obtain ⟨D, e, h24, hu, hpos, hpair⟩ :=
    _root_.D5.S3.Arith.Lattices.Golay.RealLeech.exists_positive_even_unimodular_gram
  exact law D hu h24 0 0 0 0 0 0 (-2) 0 0 (by norm_num) 0 0 (by simp) 0 0 0 0 (by simp) (by simp)
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_source_finite_cancellation)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_source_finite_cancellation, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_source_finite_cancellation)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_source_finite_cancellation "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients.mixed_source_finite_cancellation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end mixed_source_finite_cancellation

namespace mixed_first_input_branch_reindexed
def arena : Arena where
  signature := complexSignature
  Law observed := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (b : fixedGrade D E) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (N : ℕ) (hN : ((H : ℤ)+d-r-2).toNat ≤ N),
    observed.readout () ()
      ((∑ᶠ j : ℕ, Ring.choose (m : ℂ) j *
      (normalizedCoefficient D hu (m+n-(j : ℤ))
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[r+(j : ℤ)]]) u) v) E b))
      (∑ p ∈ Finset.range (K-1), ∑ i ∈ Finset.range N, ∑ L ∈ Finset.range N,
      (((-1 : ℂ)^(m+n+r+2-(p : ℤ)-(H : ℤ)-d+(i : ℤ)+(L : ℤ)))/
        ((p.factorial : ℂ)*(i.factorial : ℂ)*(L.factorial : ℂ))) *
      (∑ k ∈ Finset.range N,
        ((-1 : ℂ)^k * Ring.choose ((2*d-(L : ℤ)-m-r-2 : ℤ) : ℂ) k) *
        actualForm D hu ((T D hu ^ p) v.val)
          ((correctedField D hu b.val).coeff
            (-2*((2*(H : ℤ)-n-r-2+(p : ℤ)-(i : ℤ))+
              (2*d-(L : ℤ)-m-r-2)-(k : ℤ))-2)
            ((correctedField D hu ((originalL1 D ^ L) a.val)).coeff
              (-2*(r+(k : ℤ))-2) ((T D hu ^ i) u.val)))))

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_first_input_branch_reindexed)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro law
  obtain ⟨D, e, h24, hu, hpos, hpair⟩ :=
    _root_.D5.S3.Arith.Lattices.Golay.RealLeech.exists_positive_even_unimodular_gram
  exact law D hu h24 0 0 0 0 0 0 0 0 0 0 0 (by simp) (by simp) 0 (by simp)
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_first_input_branch_reindexed)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_first_input_branch_reindexed, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_first_input_branch_reindexed)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_first_input_branch_reindexed "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients.mixed_first_input_branch_reindexed.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end mixed_first_input_branch_reindexed

namespace mixed_second_input_reindexed_pairing
def arena : Arena where
  signature := complexSignature
  Law observed := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (b : fixedGrade D E)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (j N : ℕ) (hN : ((K : ℤ)+d-m-2).toNat ≤ N),
    observed.readout () ()
      (normalizedCoefficient D hu (n+r-(j : ℤ)) u
      (((fixedParitySlice D hu (-1)
        (⟨a.val,a.property.2⟩ : FixedCarrier D))[[m+(j : ℤ)]]) v) E b)
      (∑ q ∈ Finset.range (H-1), ∑ i ∈ Finset.range N,
      ∑ ell ∈ Finset.range N, ∑ h ∈ Finset.range N, ∑ᶠ z : ℕ,
        (((-1 : ℂ)^(n+r-(j : ℤ)+1-(i : ℤ)-(H : ℤ)+(q : ℤ)+d-
          2*(ell : ℤ)-(h : ℤ)))/
          ((i.factorial : ℂ)*(q.factorial : ℂ)*(ell.factorial : ℂ)*(z.factorial : ℂ))) *
        Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
        actualForm D hu ((T D hu ^ i) v.val)
          ((correctedField D hu ((originalL1 D ^ (ell+z)) a.val)).coeff
            (-2*(r+(2*d-((ell+z : ℕ) : ℤ)-m-r-2)-((j+ell+h : ℕ) : ℤ))-2)
            ((correctedField D hu b.val).coeff
              (-2*((2*(H : ℤ)-n-r-2+(i : ℤ)-(q : ℤ))+
                ((j+ell+h : ℕ) : ℤ))-2) ((T D hu ^ q) u.val))))

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_second_input_reindexed_pairing)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro law
  obtain ⟨D, e, h24, hu, hpos, hpair⟩ :=
    _root_.D5.S3.Arith.Lattices.Golay.RealLeech.exists_positive_even_unimodular_gram
  exact law D hu h24 0 0 0 0 0 0 (-2) 0 0 (by norm_num) 0 0 (by simp) (by simp) 0 0 (by simp)
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_second_input_reindexed_pairing)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_second_input_reindexed_pairing, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_second_input_reindexed_pairing)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_second_input_reindexed_pairing "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients.mixed_second_input_reindexed_pairing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end mixed_second_input_reindexed_pairing

namespace mixed_second_source_factorial_contraction
def arena : Arena where
  signature := complexSignature
  Law observed := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (H : ℕ) (d m n r : ℤ) (a b : Carrier D) (u v : ActualTensor D hu)
    (i q j h N : ℕ)
    (hN : a.support.sup
      (fun c => MvPolynomial.weightedTotalDegree
        (LatticeHalfFockFiniteCorrection.sourceWeight D) (a c))+1 ≤ N),
    observed.readout () ()
      ((∑ ell ∈ Finset.range N, ∑ z ∈ Finset.range N,
      ((ell.factorial : ℂ)⁻¹ * (z.factorial : ℂ)⁻¹) *
      (Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
        actualForm D hu ((T D hu ^ i) v)
          ((correctedField D hu ((originalL1 D ^ (ell+z)) a)).coeff
            (-2*(r+(2*d-((ell+z : ℕ) : ℤ)-m-r-2)-((j+ell+h : ℕ) : ℤ))-2)
            ((correctedField D hu b).coeff
              (-2*((2*(H : ℤ)-n-r-2+(i : ℤ)-(q : ℤ))+
                ((j+ell+h : ℕ) : ℤ))-2) ((T D hu ^ q) u))))))
      (∑ L ∈ Finset.range N, (L.factorial : ℂ)⁻¹ *
      (∑ ell ∈ Finset.range N, Ring.choose (L : ℂ) ell *
        Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
        actualForm D hu ((T D hu ^ i) v)
          ((correctedField D hu ((originalL1 D ^ L) a)).coeff
            (-2*(r+(2*d-(L : ℤ)-m-r-2)-((j+ell+h : ℕ) : ℤ))-2)
            ((correctedField D hu b).coeff
              (-2*((2*(H : ℤ)-n-r-2+(i : ℤ)-(q : ℤ))+
                ((j+ell+h : ℕ) : ℤ))-2) ((T D hu ^ q) u)))))

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_second_source_factorial_contraction)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro law
  obtain ⟨D, e, h24, hu, hpos, hpair⟩ :=
    _root_.D5.S3.Arith.Lattices.Golay.RealLeech.exists_positive_even_unimodular_gram
  exact law D hu 0 0 0 0 0 0 0 0 0 0 0 0 0 1 (by simp)
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_second_source_factorial_contraction)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_second_source_factorial_contraction, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_second_source_factorial_contraction)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.mixed_second_source_factorial_contraction "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients.mixed_second_source_factorial_contraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end mixed_second_source_factorial_contraction

end Reg.D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients
