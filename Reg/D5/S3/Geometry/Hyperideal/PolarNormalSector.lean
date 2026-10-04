import D5.S3.Geometry.Hyperideal.PolarNormalSector
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Geometry.Hyperideal.PolarNormalSector
open _root_.D5.S3.Geometry.Hyperideal.PolarNormalSector
open _root_.D5.S3.Geometry.Hyperideal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

local instance : AddCommGroup Space :=
  (inferInstance : NormedAddCommGroup Space).toAddCommGroup
local instance : Module ℝ Space :=
  (inferInstance : NormedSpace ℝ Space).toModule
local instance : TopologicalSpace Space :=
  (inferInstance : PseudoMetricSpace Space).toUniformSpace.toTopologicalSpace

private def hadamard : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,1,1,1;1,1,-1,-1;1,-1,1,-1;1,-1,-1,1]

private def coordEquiv (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Fin 4 → ℝ) ≃ₗ[ℝ] Space where
  toFun f := (a * ∑ i, f i,
    WithLp.toLp 2 (fun k => b * ∑ i, hadamard (k.succ) i * f i))
  invFun p := fun i => p.1/(4*a) +
    (∑ k : Fin 3, hadamard (k.succ) i * p.2 k)/(4*b)
  map_add' := by
    intro f g
    apply Prod.ext
    · simp [Finset.sum_add_distrib] <;> ring
    · apply WithLp.ofLp_injective
      funext k
      simp [mul_add,Finset.sum_add_distrib] <;> ring
  map_smul' := by
    intro r f
    apply Prod.ext
    · simp [Fin.sum_univ_four] <;> ring
    · apply WithLp.ofLp_injective
      funext k
      simp [Fin.sum_univ_four] <;> ring
  left_inv := by
    intro f
    funext i
    fin_cases i <;>
      simp [hadamard,Fin.sum_univ_four,Fin.sum_univ_three] <;>
      field_simp [ha,hb] <;> ring
  right_inv := by
    intro p
    apply Prod.ext
    · simp [hadamard,Fin.sum_univ_four,Fin.sum_univ_three]
      field_simp [ha,hb] <;> ring
    · apply WithLp.ofLp_injective
      funext k
      fin_cases k <;>
        simp [hadamard,Fin.sum_univ_four,Fin.sum_univ_three] <;>
        field_simp [ha,hb] <;> ring

private def witnessFrame : GramFrame := by
  let t := Real.sqrt 11
  have ht : 0 < t := Real.sqrt_pos.mpr (by norm_num)
  have ht2 : t^2=11 := Real.sq_sqrt (by norm_num)
  have hvt : t/4 ≠ 0 := by positivity
  have hvs : (3/4 : ℝ) ≠ 0 := by norm_num
  have hwt : -t⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero ht.ne')
  have hws : (1/3 : ℝ) ≠ 0 := by norm_num
  let V := (Pi.basisFun ℝ (Fin 4)).map (coordEquiv (t/4) (3/4) hvt hvs)
  let W := (Pi.basisFun ℝ (Fin 4)).map (coordEquiv (-t⁻¹) (1/3) hwt hws)
  refine ⟨fun _ _ => 5/4,V,W,?_,?_,?_⟩
  · intro i j
    change -((coordEquiv (t/4) (3/4) hvt hvs) (Pi.basisFun ℝ (Fin 4) i)).1 *
      ((coordEquiv (t/4) (3/4) hvt hvs) (Pi.basisFun ℝ (Fin 4) j)).1 +
      inner ℝ ((coordEquiv (t/4) (3/4) hvt hvs) (Pi.basisFun ℝ (Fin 4) i)).2
        ((coordEquiv (t/4) (3/4) hvt hvs) (Pi.basisFun ℝ (Fin 4) j)).2 = _
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply,Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;>
      simp [coordEquiv,hadamard,Pi.basisFun_apply,Pi.single_apply,
        PiLp.inner_apply,Real.inner_apply,Fin.sum_univ_four,Fin.sum_univ_three] <;>
      nlinarith only [ht2]
  · intro i j
    change -((coordEquiv (t/4) (3/4) hvt hvs) (Pi.basisFun ℝ (Fin 4) i)).1 *
      ((coordEquiv (-t⁻¹) (1/3) hwt hws) (Pi.basisFun ℝ (Fin 4) j)).1 +
      inner ℝ ((coordEquiv (t/4) (3/4) hvt hvs) (Pi.basisFun ℝ (Fin 4) i)).2
        ((coordEquiv (-t⁻¹) (1/3) hwt hws) (Pi.basisFun ℝ (Fin 4) j)).2 = _
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply,Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;>
      simp [coordEquiv,hadamard,Pi.basisFun_apply,Pi.single_apply,
        PiLp.inner_apply,Real.inner_apply,Fin.sum_univ_four,Fin.sum_univ_three] <;>
      field_simp <;> ring
  · intros; norm_num

/-- All frame, ordering and real edge-position parameters remain variable. -/
abbrev signature : Signature where
  Params := Σ _ : GramFrame, Σ _ : Equiv.Perm (Fin 4), ℝ
  State _ := Space
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p u => u ∈ forwardNormalSet p.1 p.2.1 p.2.2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

/-- Only the selected forward-predicate occurrence is intervened upon. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (F : GramFrame)  (e : Equiv.Perm (Fin 4))
    (s : ℝ) (hs : 0 < s ∧ s < Real.arcosh (F.lengths (e 0) (e 1))) ,
    edgePoint F e s ∈ polarSet F ∧
    lorentz (edgeVelocity F e s) (edgeVelocity F e s)=1 ∧
    lorentz (edgePoint F e s) (edgeVelocity F e s)=0 ∧
    (∀ u : Space, u ∈ normalSpace F e s ↔
      ∃ α β : ℝ, u=α • dualVertex F (e 2)+β • dualVertex F (e 3)) ∧
    Module.finrank ℝ (normalSpace F e s)=2 ∧
    (∀ u : Space, R.readout () ⟨F,e,s⟩ u ↔
      ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
        u=α • inwardRay F e false+β • inwardRay F e true) ∧
    lorentz (inwardRay F e false) (inwardRay F e false)=1 ∧
    lorentz (inwardRay F e true) (inwardRay F e true)=1 ∧
    0 < 1-(normalCosine F e)^2 ∧
    (let D := -(gramMatrix F e).det
     let A := FourCycleEnvelopes.rad (F.lengths (e 0) (e 1))
       (F.lengths (e 0) (e 2)) (F.lengths (e 1) (e 2))
     let B := FourCycleEnvelopes.rad (F.lengths (e 0) (e 1))
       (F.lengths (e 0) (e 3)) (F.lengths (e 1) (e 3))
     let P := FourCycleEnvelopes.numerator (F.lengths (e 0) (e 1))
       (F.lengths (e 0) (e 2)) (F.lengths (e 0) (e 3))
       (F.lengths (e 2) (e 3)) (F.lengths (e 1) (e 3)) (F.lengths (e 1) (e 2))
     0 < D ∧ D=((frameMatrix F e).det)^2 ∧
       lorentz (dualVertex F (e 2)) (dualVertex F (e 2))=B/D ∧
       lorentz (dualVertex F (e 3)) (dualVertex F (e 3))=A/D ∧
       lorentz (dualVertex F (e 2)) (dualVertex F (e 3))= -P/D ∧
       A*B-P^2=((F.lengths (e 0) (e 1))^2-1)*D) ∧
    (∀ q u : Space, lorentz q q = -1 → lorentz q u = 0 →
      inner ℝ u.2 u.2 ≤ q.1^2 * lorentz u u ∧
      (lorentz u u = 0 ↔ u = 0)) ∧
    HasDerivAt (edgePoint F e) (edgeVelocity F e s) s ∧
    ((∀ i : Fin 4, lorentz (edgePoint F e s) (dualVertex F (e i)) =
        (Real.sinh (Real.arcosh (F.lengths (e 0) (e 1))))⁻¹ *
        (Real.cosh (Real.arcosh (F.lengths (e 0) (e 1))-s) * (if i=0 then 1 else 0) +
         Real.cosh s * (if i=1 then 1 else 0))) ∧
      lorentz (edgePoint F e s) (vertex F (e 0)) = -Real.sinh s ∧
      lorentz (edgePoint F e s) (vertex F (e 1)) =
        -Real.sinh (Real.arcosh (F.lengths (e 0) (e 1))-s) ∧
      (∀ i : Fin 4, lorentz (edgePoint F e s) (vertex F (e i)) < 0) ∧
      (∀ i : Fin 4, i=2 ∨ i=3 →
        lorentz (edgePoint F e s) (vertex F (e i)) =
        -(F.lengths (e 0) (e i)*Real.cosh (Real.arcosh (F.lengths (e 0) (e 1))-s) +
          F.lengths (e 1) (e i)*Real.cosh s) /
          Real.sinh (Real.arcosh (F.lengths (e 0) (e 1))))) ∧
    (∀ u : Space, u ∈ forwardNormalSet F e s ↔
      u ∈ normalSpace F e s ∧ lorentz u (outwardNormal F (e 2)) ≤ 0 ∧
        lorentz u (outwardNormal F (e 3)) ≤ 0) ∧
    lorentz (inwardRay F e false) (inwardRay F e true) =
      FourCycleEnvelopes.cosine (F.lengths (e 0) (e 1))
        (F.lengths (e 0) (e 2)) (F.lengths (e 0) (e 3))
        (F.lengths (e 2) (e 3)) (F.lengths (e 1) (e 3)) (F.lengths (e 1) (e 2)) ∧
    ∃ (hp : lorentz (edgePoint F e s) (edgePoint F e s) = -1)
      (h₂ : lorentz (edgePoint F e s) (inwardRay F e false) = 0)
      (h₃ : lorentz (edgePoint F e s) (inwardRay F e true) = 0),
      tangentAngle (edgePoint F e s) hp ⟨inwardRay F e false,h₂⟩
        ⟨inwardRay F e true,h₃⟩ = Real.arccos (FourCycleEnvelopes.cosine (F.lengths (e 0) (e 1))
        (F.lengths (e 0) (e 2)) (F.lengths (e 0) (e 3))
        (F.lengths (e 2) (e 3)) (F.lengths (e 1) (e 3)) (F.lengths (e 1) (e 2)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let e : Equiv.Perm (Fin 4) := Equiv.refl _
  let L := Real.arcosh (witnessFrame.lengths (e 0) (e 1))
  have hL : 0 < L := Real.arcosh_pos (by norm_num [witnessFrame,e])
  have hs : 0 < L/2 ∧ L/2 < Real.arcosh (witnessFrame.lengths (e 0) (e 1)) := by
    change 0<L/2 ∧ L/2<L
    constructor <;> linarith only [hL]
  have hsector := (h witnessFrame e (L/2) hs).2.2.2.2.2.1
  have impossible := (hsector 0).mpr ⟨0,0,le_refl 0,le_refl 0,by simp⟩
  exact impossible

private theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  let e : Equiv.Perm (Fin 4) := Equiv.refl _
  let L := Real.arcosh (witnessFrame.lengths (e 0) (e 1))
  have hL : 0 < L := Real.arcosh_pos (by norm_num [witnessFrame,e])
  have hs : 0 < L/2 ∧ L/2 < Real.arcosh (witnessFrame.lengths (e 0) (e 1)) := by
    change 0<L/2 ∧ L/2<L
    constructor <;> linarith only [hL]
  have h := polar_edge_forward_sector witnessFrame e (L/2) hs
  have hzero : (0 : Space) ∈ forwardNormalSet witnessFrame e (L/2) :=
    (h.2.2.2.2.2.1 0).mpr ⟨0,0,le_refl 0,le_refl 0,by simp⟩
  have hpoint : edgePoint witnessFrame e (L/2) ∉ forwardNormalSet witnessFrame e (L/2) := by
    intro hp
    have he := hp.1
    rw [h.1.1] at he
    norm_num at he
  refine ⟨⟨witnessFrame,e,L/2⟩,0,edgePoint witnessFrame e (L/2),?_⟩
  change ((0 : Space) ∈ forwardNormalSet witnessFrame e (L/2)) ≠
    (edgePoint witnessFrame e (L/2) ∈ forwardNormalSet witnessFrame e (L/2))
  intro he
  exact hpoint (he ▸ hzero)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨polar_edge_forward_sector,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := dependence_proof

register_information_theorem polar_edge_forward_sector in arena
  readout via (realize signature
    (fun _ p u => u ∈ forwardNormalSet p.1 p.2.1 p.2.2) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Geometry.Hyperideal.PolarNormalSector
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","arg","arg","arg","arg","arg",
        "fn","arg","body","fn","arg"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms registration
end
end Reg.D5.S3.Geometry.Hyperideal.PolarNormalSector
