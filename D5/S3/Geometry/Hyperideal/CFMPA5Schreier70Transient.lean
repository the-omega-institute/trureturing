import D5.S3.FiniteGroups.CFMPNormalizerCentralizer
import D5.S3.Geometry.Hyperideal.A5CosetPacket
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.List
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic
import Lean.Util.CollectAxioms

/- Uncompiled source candidate for the exact original twelve-coset action. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CFMPA5Schreier70Transient

open D5.S3.FiniteGroups.CFMPNormalizerCentralizer
namespace Packet
open D5.S3.Geometry.Hyperideal.A5CosetPacket

abbrev A5 := alternatingGroup (Fin 5)

def u : A5 := ⟨([2,3,4] : List (Fin 5)).formPerm, by decide⟩
def v : A5 := ⟨([0,2,4,1,3] : List (Fin 5)).formPerm, by decide⟩

def representative : Fin 12 → A5 :=
  ![1, u, u^2, u^2*v^2*u, u^2*v^2, u^2*v*u^2*v,
    u^2*v*u, u^2*v*u^2, u^2*v,
    u^2*v*u^2*v^2*u, u^2*v*u^2*v^2, u^2*v*u^2*v^2*u^2]

def uCorrection : Fin 12 → ℕ := ![0,0,0,4,0,1,0,0,0,0,0,0]
def vCorrection : Fin 12 → ℕ := ![4,1,0,0,4,0,0,0,0,1,4,1]

def coordinate (p : Fin 5 × Fin 12) : A5 := v ^ p.1.val * representative p.2

def cyclicSubgroup : Subgroup A5 := Subgroup.zpowers v

def quotientPoint (i : Fin 12) : RightCosets cyclicSubgroup :=
  Quotient.mk'' (representative i)

example :
    orderOf v = 5 ∧
    Subgroup.closure ({u,v} : Set A5) = ⊤ ∧
    ∃ e : Fin 12 ≃ RightCosets cyclicSubgroup,
      (∀ i, e i = quotientPoint i) ∧
      (∀ i, e (U i) = rightMul cyclicSubgroup u (e i)) ∧
      (∀ i, e (V i) = rightMul cyclicSubgroup v (e i)) := by
  let hwhole :
      orderOf v = 5 ∧
      Subgroup.closure ({u,v} : Set A5) = ⊤ ∧
      ∃ e : Fin 12 ≃ RightCosets cyclicSubgroup,
        (∀ i, e i = quotientPoint i) ∧
        (∀ i, e (U i) = rightMul cyclicSubgroup u (e i)) ∧
        (∀ i, e (V i) = rightMul cyclicSubgroup v (e i)) := by
    have certificate :
        v ^ 5 = 1 ∧ v ≠ 1 ∧ Function.Injective coordinate ∧
        (∀ i, representative (U i) = v ^ uCorrection i * representative i * u) ∧
        (∀ i, representative (V i) = v ^ vCorrection i * representative i * v) := by
      decide +kernel
    rcases certificate with ⟨h5,hne,hinj,hU,hV⟩
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hord : orderOf v = 5 := orderOf_eq_prime h5 hne
    have hcard : Fintype.card (Fin 5 × Fin 12) = Fintype.card A5 := by
      norm_num [A5, card_alternatingGroup]
    have hsurj : Function.Surjective coordinate :=
      ((Fintype.bijective_iff_injective_and_card coordinate).mpr ⟨hinj,hcard⟩).2
    have hgen : Subgroup.closure ({u,v} : Set A5) = ⊤ := by
      let L := Subgroup.closure ({u,v} : Set A5)
      have hu : u ∈ L := Subgroup.subset_closure (by simp)
      have hv : v ∈ L := Subgroup.subset_closure (by simp)
      have hu2 : u ^ 2 ∈ L := L.pow_mem hu 2
      have hv2 : v ^ 2 ∈ L := L.pow_mem hv 2
      have hr : ∀ i, representative i ∈ L := by
        intro i
        fin_cases i <;> dsimp [representative]
        all_goals repeat' first | assumption | exact L.one_mem | apply L.mul_mem
      apply top_unique
      intro g _
      obtain ⟨⟨n,i⟩,rfl⟩ := hsurj g
      exact L.mul_mem (L.pow_mem hv n.val) (hr i)
    have hqi : Function.Injective quotientPoint := by
      intro i j hij
      have hrel := Quotient.exact' hij
      rw [QuotientGroup.rightRel_apply] at hrel
      change representative j * (representative i)⁻¹ ∈ Subgroup.zpowers v at hrel
      rw [mem_zpowers_iff_mem_range_orderOf, hord, Finset.mem_image] at hrel
      obtain ⟨n,hn,he⟩ := hrel
      have hn' : n < 5 := Finset.mem_range.mp hn
      have hcoord : coordinate (⟨n,hn'⟩,i) = coordinate (0,j) := by
        dsimp [coordinate]
        rw [he]
        simp [mul_assoc]
      exact congrArg Prod.snd (hinj hcoord)
    have hqs : Function.Surjective quotientPoint := by
      intro q
      refine Quotient.inductionOn' q ?_
      intro g
      obtain ⟨⟨n,i⟩,rfl⟩ := hsurj g
      refine ⟨i,Quotient.sound' ?_⟩
      rw [QuotientGroup.rightRel_apply]
      change (v ^ n.val * representative i) * (representative i)⁻¹ ∈ cyclicSubgroup
      simpa [mul_assoc,cyclicSubgroup] using
        (Subgroup.pow_mem (Subgroup.zpowers v) (Subgroup.mem_zpowers v) n.val)
    let e : Fin 12 ≃ RightCosets cyclicSubgroup := Equiv.ofBijective quotientPoint ⟨hqi,hqs⟩
    refine ⟨hord,hgen,e,fun _ => rfl,?_,?_⟩
    · intro i
      change Quotient.mk'' (representative (U i)) =
        Quotient.mk'' (representative i * u)
      apply Quotient.sound'
      rw [QuotientGroup.rightRel_apply,hU]
      change (representative i * u) *
        (v ^ uCorrection i * representative i * u)⁻¹ ∈ cyclicSubgroup
      simpa [mul_assoc,cyclicSubgroup] using
        (Subgroup.inv_mem (Subgroup.zpowers v)
          (Subgroup.pow_mem (Subgroup.zpowers v) (Subgroup.mem_zpowers v) (uCorrection i)))
    · intro i
      change Quotient.mk'' (representative (V i)) =
        Quotient.mk'' (representative i * v)
      apply Quotient.sound'
      rw [QuotientGroup.rightRel_apply,hV]
      change (representative i * v) *
        (v ^ vCorrection i * representative i * v)⁻¹ ∈ cyclicSubgroup
      simpa [mul_assoc,cyclicSubgroup] using
        (Subgroup.inv_mem (Subgroup.zpowers v)
          (Subgroup.pow_mem (Subgroup.zpowers v) (Subgroup.mem_zpowers v) (vCorrection i)))
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let whole ← Lean.Meta.getLocalDeclFromUserName `hwhole
      let some raw := whole.value? |
        Lean.throwError "A5SCHREIER70: missing whole proof value"
      let proof ← Lean.instantiateMVars raw
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let proofType ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
      if proof.hasMVar || target.hasMVar || proofType.hasMVar then
        Lean.throwError "A5SCHREIER70: unresolved metavariables"
      if proof.hasFVar || target.hasFVar || proofType.hasFVar then
        Lean.throwError "A5SCHREIER70: unexpected free assumptions"
      if proof.hasLooseBVars || target.hasLooseBVars || proofType.hasLooseBVars then
        Lean.throwError "A5SCHREIER70: loose bound variables"
      unless ← Lean.Meta.isDefEq proofType target do
        Lean.throwError "A5SCHREIER70: whole proof differs from the exact target"
      let mut constants : Lean.NameSet := {}
      for constant in proof.getUsedConstants do constants := constants.insert constant
      for constant in proofType.getUsedConstants do constants := constants.insert constant
      let env := (← Lean.getEnv).setExporting false
      let mut axioms : Lean.NameSet := {}
      for constant in constants.toArray.qsort Lean.Name.lt do
        if (env.checked.get.find? constant).isNone then
          Lean.throwError m!"A5SCHREIER70: unchecked constant {constant}"
        for axiomName in ← Lean.collectAxioms constant do
          axioms := axioms.insert axiomName
      let axiomNames := axioms.toArray.qsort Lean.Name.lt
      let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
      for axiomName in axiomNames do
        unless allowed.contains axiomName do
          Lean.throwError m!"A5SCHREIER70: disallowed axiom {axiomName}"
      let names := String.intercalate ", " (axiomNames.toList.map toString)
      Lean.logInfo m!"CFMP_A5_SCHREIER70 exact_axioms=[{names}] constant_count={constants.toArray.size} original_parameter_count=0"
  exact hwhole

end Packet
end CFMPA5Schreier70Transient
