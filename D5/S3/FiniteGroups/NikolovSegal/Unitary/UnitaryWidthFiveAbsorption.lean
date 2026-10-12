/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthFiveAbsorption
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthFiveAbsorption
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthLeviExtraction
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthRadicalNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-! Constant-length Hermitian rank reduction. Every radical is the literal
boundary subgroup, and all conjugations used in absorption are proved to stay
inside that actual SU radical. The five slots never grow with the rank. -/
namespace NikolovSegal.UnitaryWholeGroupWidth
open Matrix UnitarySylow
universe u
variable {F : Type u} [Field F] {n : ℕ} {ι : RingAut F}

def FiveFactor (g : specialUnitary n ι) : Prop :=
  ∃ a b c d e : specialUnitary n ι,
    Positive a ∧ Negative b ∧ Positive c ∧ Negative d ∧ Positive e ∧ a*b*c*d*e=g

/-- Move the five triangular Levi cores to the left. No arbitrary triangular
factor is treated as a radical; each is decomposed by its genuine SU theorem. -/
theorem five_triangular_core_radicals (x0 x1 x2 x3 x4 : specialUnitary (n+2) ι)
    (h0 : Positive x0) (h1 : Negative x1) (h2 : Positive x2)
    (h3 : Negative x3) (h4 : Positive x4) :
    ∃ B : specialUnitary n ι, ∃ r0 r1 r2 r3 r4 : specialUnitary (n+2) ι,
      UpRadical r0 ∧ DownRadical r1 ∧ UpRadical r2 ∧ DownRadical r3 ∧
      UpRadical r4 ∧ x0*x1*x2*x3*x4=centralEmbed B*r0*r1*r2*r3*r4 := by
  obtain ⟨b0,v0,_,hv0,e0⟩ := positive_levi_radical h0
  obtain ⟨b1,v1,_,hv1,e1⟩ := negative_levi_radical h1
  obtain ⟨b2,v2,_,hv2,e2⟩ := positive_levi_radical h2
  obtain ⟨b3,v3,_,hv3,e3⟩ := negative_levi_radical h3
  obtain ⟨b4,v4,_,hv4,e4⟩ := positive_levi_radical h4
  let s0 := b1*b2*b3*b4
  let s1 := b2*b3*b4
  let s2 := b3*b4
  refine ⟨b0*b1*b2*b3*b4,
    centralEmbed s0⁻¹*v0*(centralEmbed s0⁻¹)⁻¹,
    centralEmbed s1⁻¹*v1*(centralEmbed s1⁻¹)⁻¹,
    centralEmbed s2⁻¹*v2*(centralEmbed s2⁻¹)⁻¹,
    centralEmbed b4⁻¹*v3*(centralEmbed b4⁻¹)⁻¹,v4,
    central_conjugate_upRadical s0⁻¹ hv0,
    central_conjugate_downRadical s1⁻¹ hv1,
    central_conjugate_upRadical s2⁻¹ hv2,
    central_conjugate_downRadical b4⁻¹ hv3,hv4,?_⟩
  rw [←e0,←e1,←e2,←e3,←e4]
  simp only [s0,s1,s2,map_mul,map_inv]
  group

/-- Genuine higher-rank reduction with exactly five ordered boundary radicals. -/
theorem higher_rank_five_radicals [Finite F] {k : ℕ}
    (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (g : specialUnitary (k+4) ι) :
    ∃ B : specialUnitary (k+2) ι, ∃ r0 r1 r2 r3 r4 : specialUnitary (k+4) ι,
      UpRadical r0 ∧ DownRadical r1 ∧ UpRadical r2 ∧ DownRadical r3 ∧
      UpRadical r4 ∧ centralEmbed B*r0*r1*r2*r3*r4=g := by
  obtain ⟨u,l,v,m,hu,hl,hv,hm,hrow,hcol⟩ := four_operations_endpoint_stabilizer hinv hne g
  have he : Endpoints (g*u*l*v*m).val := ⟨hcol,hrow⟩
  obtain ⟨B,w,hw,heq⟩ := endpoint_levi_radical (g*u*l*v*m) he
  obtain ⟨C,r0,r1,r2,r3,r4,hr0,hr1,hr2,hr3,hr4,hh⟩ :=
    five_triangular_core_radicals w m⁻¹ v⁻¹ l⁻¹ u⁻¹
      (upRadical_positive hw) (negative_inv hm) (positive_inv hv) (negative_inv hl) (positive_inv hu)
  refine ⟨B*C,r0,r1,r2,r3,r4,hr0,hr1,hr2,hr3,hr4,?_⟩
  calc
    _ = centralEmbed B*(centralEmbed C*r0*r1*r2*r3*r4) := by rw [map_mul]; group
    _ = centralEmbed B*(w*m⁻¹*v⁻¹*l⁻¹*u⁻¹) := by rw [←hh]
    _ = (centralEmbed B*w)*m⁻¹*v⁻¹*l⁻¹*u⁻¹ := by group
    _ = g := by rw [heq]; group

/-- Absorption is constant length: arbitrary central SU normalizes BOTH actual
radicals, so the five ordered slots retain their triangular orientations. -/
theorem five_factor_absorb {B : specialUnitary n ι} (hB : FiveFactor B)
    {r0 r1 r2 r3 r4 : specialUnitary (n+2) ι}
    (h0 : UpRadical r0) (h1 : DownRadical r1) (h2 : UpRadical r2)
    (h3 : DownRadical r3) (h4 : UpRadical r4) :
    FiveFactor (centralEmbed B*r0*r1*r2*r3*r4) := by
  obtain ⟨a,b,c,d,e,ha,hb,hc,hd,he,heq⟩ := hB
  let s0 := b*c*d*e
  let s1 := c*d*e
  let s2 := d*e
  refine ⟨centralEmbed a*(centralEmbed s0*r0*(centralEmbed s0)⁻¹),
    centralEmbed b*(centralEmbed s1*r1*(centralEmbed s1)⁻¹),
    centralEmbed c*(centralEmbed s2*r2*(centralEmbed s2)⁻¹),
    centralEmbed d*(centralEmbed e*r3*(centralEmbed e)⁻¹),
    centralEmbed e*r4,
    positive_mul (centralEmbed_positive ha) (upRadical_positive (central_conjugate_upRadical s0 h0)),
    negative_mul (centralEmbed_negative hb) (downRadical_negative (central_conjugate_downRadical s1 h1)),
    positive_mul (centralEmbed_positive hc) (upRadical_positive (central_conjugate_upRadical s2 h2)),
    negative_mul (centralEmbed_negative hd) (downRadical_negative (central_conjugate_downRadical e h3)),
    positive_mul (centralEmbed_positive he) (upRadical_positive h4),?_⟩
  rw [←heq]
  simp only [s0,s1,s2,map_mul]
  group

end NikolovSegal.UnitaryWholeGroupWidth
