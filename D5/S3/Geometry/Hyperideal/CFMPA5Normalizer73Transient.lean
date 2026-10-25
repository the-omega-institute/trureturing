import D5.S3.FiniteGroups.CFMPNormalizerCentralizer
import D5.S3.Arith.IcosahedralAxisDecomposition
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Perm.List
import Mathlib.Tactic
import Lean.Util.CollectAxioms

/- Temporary exact application; not a retained mathematical declaration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CFMPA5Normalizer73Transient

open D5.S3.FiniteGroups.CFMPNormalizerCentralizer
open D5.S3.Arith.IcosahedralAxisDecomposition

abbrev A5 := alternatingGroup (Fin 5)

def u : A5 := ⟨([2,3,4] : List (Fin 5)).formPerm, by decide⟩
def v : A5 := ⟨([0,2,4,1,3] : List (Fin 5)).formPerm, by decide⟩
def C : Subgroup A5 := Subgroup.zpowers v
def w : A5 := v ^ 3

example :
    ¬ C.Normal ∧
    Nat.card (Subgroup.normalizer (C : Set A5)) = 10 ∧
    Nat.card (commutingPerms C) = 2 ∧
    ¬ ∃ p : commutingPerms C,
      p.1 (Quotient.mk'' (1 : A5)) = Quotient.mk'' u := by
  classical
  let hwhole :
      ¬ C.Normal ∧
      Nat.card (Subgroup.normalizer (C : Set A5)) = 10 ∧
      Nat.card (commutingPerms C) = 2 ∧
      ¬ ∃ p : commutingPerms C,
        p.1 (Quotient.mk'' (1 : A5)) = Quotient.mk'' u := by
    have metadata :
        v ^ 5 = 1 ∧ v ≠ 1 ∧ w ^ 2 = v ∧
        IsCanonicalCyclicAxis 5 w ∧
        u * v * u⁻¹ ∉ cyclicAxis 5 w := by
      decide +kernel
    rcases metadata with ⟨hv5,hvne,hw2,hcanonical,houtside⟩
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hvOrder : orderOf v = 5 := orderOf_eq_prime hv5 hvne
    have hwOrder : orderOf w = 5 :=
      orderOf_eq_prime hcanonical.1.2 hcanonical.1.1
    have hCw : C = Subgroup.zpowers w := by
      apply le_antisymm
      · change Subgroup.zpowers v ≤ Subgroup.zpowers w
        apply Subgroup.zpowers_le_of_mem
        rw [← hw2]
        exact (Subgroup.zpowers w).pow_mem (Subgroup.mem_zpowers w) 2
      · apply Subgroup.zpowers_le_of_mem
        exact C.pow_mem (Subgroup.mem_zpowers v) 3
    have hfinite (x : A5) : x ∈ cyclicAxis 5 w ↔ x ∈ C := by
      rw [hCw, mem_zpowers_iff_mem_range_orderOf, hwOrder]
      rfl
    have hwmem : w ∈ C := by
      rw [hCw]
      exact Subgroup.mem_zpowers w
    have hnormalizer (x : A5) :
        x ∈ Subgroup.normalizer (C : Set A5) ↔
          x ∈ cyclicAxisNormalizer 5 w := by
      rw [cyclicAxisNormalizer, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      rw [axisContains, hfinite]
      constructor
      · intro hx
        exact ((Subgroup.mem_normalizer_iff.mp hx) w).mp hwmem
      · intro hx
        apply Subgroup.mem_normalizer_fintype
        intro y hy
        have hy' : y ∈ Subgroup.zpowers w := hCw ▸ hy
        rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hy'
        obtain ⟨n,_,rfl⟩ := hy'
        have hp : x * w ^ n * x⁻¹ = (x * w * x⁻¹) ^ n := by
          simpa only [MulAut.conj_apply] using map_pow (MulAut.conj x) w n
        rw [hp]
        exact C.pow_mem hx n
    have hNcard : Nat.card (Subgroup.normalizer (C : Set A5)) = 10 := by
      let e : Subgroup.normalizer (C : Set A5) ≃
          {x : A5 // x ∈ cyclicAxisNormalizer 5 w} :=
        Equiv.subtypeEquivRight hnormalizer
      calc
        Nat.card (Subgroup.normalizer (C : Set A5)) =
            Nat.card {x : A5 // x ∈ cyclicAxisNormalizer 5 w} := Nat.card_congr e
        _ = (cyclicAxisNormalizer 5 w).card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        _ = 10 := icosahedral_axis_stabilizer_orders.1 ⟨w,hcanonical⟩
    have houtsideC : u * v * u⁻¹ ∉ C := by
      intro h
      exact houtside ((hfinite _).mpr h)
    have hnotnormal : ¬ C.Normal := by
      intro h
      letI : C.Normal := h
      have huN : u ∈ Subgroup.normalizer (C : Set A5) := by
        rw [Subgroup.normalizer_eq_top]
        exact Subgroup.mem_top u
      exact houtsideC (((Subgroup.mem_normalizer_iff.mp huN) v).mp
        (Subgroup.mem_zpowers v))
    have hCcard : Nat.card C = 5 := by
      simpa only [Nat.card_eq_fintype_card, C, Fintype.card_zpowers] using hvOrder
    let N := Subgroup.normalizer (C : Set A5)
    let H := C.subgroupOf N
    have hHcard : Nat.card H = 5 := by
      calc
        Nat.card H = Nat.card C :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe C.le_normalizer).toEquiv
        _ = 5 := hCcard
    have hquot : Nat.card (N ⧸ H) = 2 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup H
      change Nat.card N = Nat.card (N ⧸ H) * Nat.card H at h
      rw [hNcard,hHcard] at h
      omega
    have hcommuting : Nat.card (commutingPerms C) = 2 := by
      calc
        Nat.card (commutingPerms C) = Nat.card (N ⧸ H) :=
          (Nat.card_congr (normalizerCentralizerIso C).toEquiv).symm
        _ = 2 := hquot
    have hseparate : ¬ ∃ p : commutingPerms C,
        p.1 (Quotient.mk'' (1 : A5)) = Quotient.mk'' u := by
      rintro ⟨p,hp⟩
      have hcomm : rightMul C v * p.1 = p.1 * rightMul C v :=
        (Subgroup.mem_centralizer_iff.mp p.2) _ ⟨v,rfl⟩
      have hvfix : rightMul C v (Quotient.mk'' (1 : A5)) =
          Quotient.mk'' (1 : A5) := by
        apply Quotient.sound'
        rw [QuotientGroup.rightRel_apply]
        simpa using C.inv_mem (Subgroup.mem_zpowers v)
      have he := congrArg (fun e : Equiv.Perm (RightCosets C) =>
        e (Quotient.mk'' (1 : A5))) hcomm
      have he' : rightMul C v (Quotient.mk'' u) = Quotient.mk'' u := by
        simpa only [Equiv.Perm.mul_apply, hvfix, hp] using he
      rw [rightMul_mk] at he'
      have hr := Quotient.exact' he'
      rw [QuotientGroup.rightRel_apply] at hr
      apply houtsideC
      simpa [mul_assoc] using C.inv_mem hr
    exact ⟨hnotnormal,hNcard,hcommuting,hseparate⟩
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let whole ← Lean.Meta.getLocalDeclFromUserName `hwhole
      let some raw := whole.value? |
        Lean.throwError "A5NORMALIZER73: missing whole proof value"
      let proof ← Lean.instantiateMVars raw
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let proofType ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
      if proof.hasMVar || target.hasMVar || proofType.hasMVar then
        Lean.throwError "A5NORMALIZER73: unresolved metavariables"
      if proof.hasFVar || target.hasFVar || proofType.hasFVar then
        Lean.throwError "A5NORMALIZER73: unexpected free assumptions"
      if proof.hasLooseBVars || target.hasLooseBVars || proofType.hasLooseBVars then
        Lean.throwError "A5NORMALIZER73: loose bound variables"
      unless ← Lean.Meta.isDefEq proofType target do
        Lean.throwError "A5NORMALIZER73: whole proof differs from the exact target"
      let mut constants : Lean.NameSet := {}
      for constant in proof.getUsedConstants do constants := constants.insert constant
      for constant in proofType.getUsedConstants do constants := constants.insert constant
      let env := (← Lean.getEnv).setExporting false
      let mut axioms : Lean.NameSet := {}
      for constant in constants.toArray.qsort Lean.Name.lt do
        if (env.checked.get.find? constant).isNone then
          Lean.throwError m!"A5NORMALIZER73: unchecked constant {constant}"
        for axiomName in ← Lean.collectAxioms constant do
          axioms := axioms.insert axiomName
      let axiomNames := axioms.toArray.qsort Lean.Name.lt
      let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
      for axiomName in axiomNames do
        unless allowed.contains axiomName do
          Lean.throwError m!"A5NORMALIZER73: disallowed axiom {axiomName}"
      let names := String.intercalate ", " (axiomNames.toList.map toString)
      Lean.logInfo m!"CFMP_A5_NORMALIZER73 exact_axioms=[{names}] constant_count={constants.toArray.size} original_parameter_count=0"
  exact hwhole

end CFMPA5Normalizer73Transient
