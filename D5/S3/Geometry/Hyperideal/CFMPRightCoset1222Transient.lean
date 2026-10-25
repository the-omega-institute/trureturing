import D5.S3.FiniteGroups.CFMPNormalizerCentralizer
import Mathlib.Algebra.Group.Subgroup.MulOpposite
import Mathlib.GroupTheory.Index
import Lean.Util.CollectAxioms
import D5.S3.Geometry.Gluing.ActualCornerPointPeriods
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.GroupAction.Period
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.DoubleCoset
import D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits

section
open D5.S3.FiniteGroups.CFMPNormalizerCentralizer

noncomputable section
set_option autoImplicit false

-- Transient source candidate. No compile claim and no canonical retention.
-- The original finite and two-generator hypotheses are retained explicitly.
example {G : Type*} [groupInst : Group G] [finiteInst : Finite G] (u v : G)
    (_generates : Subgroup.closure ({u, v} : Set G) = ⊤) (C : Subgroup G) :
    let s := (u ^ 2)⁻¹ * v
    let t := (u ^ 3)⁻¹ * v * u
    let k := v * u ^ 3
    let K := Subgroup.closure ({s, t, k} : Set G)
    (∀ q r : RightCosets C, ∃ a : G, rightMul C a q = r) ∧
    ∀ g : G,
      (Set.range (fun a : K =>
        rightMul C (a : G) (Quotient.mk'' g : RightCosets C))).ncard =
      (K ⊓ C.comap (MulAut.conj g).toMonoidHom).relIndex K := by
  let hwhole :
      let s := (u ^ 2)⁻¹ * v
      let t := (u ^ 3)⁻¹ * v * u
      let k := v * u ^ 3
      let K := Subgroup.closure ({s, t, k} : Set G)
      (∀ q r : RightCosets C, ∃ a : G, rightMul C a q = r) ∧
      ∀ g : G,
        (Set.range (fun a : K =>
          rightMul C (a : G) (Quotient.mk'' g : RightCosets C))).ncard =
        (K ⊓ C.comap (MulAut.conj g).toMonoidHom).relIndex K := by
    let s := (u ^ 2)⁻¹ * v
    let t := (u ^ 3)⁻¹ * v * u
    let k := v * u ^ 3
    let K := Subgroup.closure ({s, t, k} : Set G)
    change (∀ q r : RightCosets C, ∃ a : G, rightMul C a q = r) ∧
      ∀ g : G,
        (Set.range (fun a : K =>
          rightMul C (a : G) (Quotient.mk'' g : RightCosets C))).ncard =
        (K ⊓ C.comap (MulAut.conj g).toMonoidHom).relIndex K
    -- op a acts by q ↦ q a; op a * op b = op (b*a).
    letI : MulAction Gᵐᵒᵖ (RightCosets C) where
      smul a q := rightMul C a.unop q
      one_smul q := by
        refine Quotient.inductionOn' q ?_
        intro g
        change Quotient.mk'' (g * (1 : G)) = Quotient.mk'' g
        simp
      mul_smul a b q := by
        refine Quotient.inductionOn' q ?_
        intro g
        change Quotient.mk'' (g * (b.unop * a.unop)) =
          Quotient.mk'' ((g * b.unop) * a.unop)
        congr 1
        exact (mul_assoc g b.unop a.unop).symm
    constructor
    · intro q r
      refine Quotient.inductionOn' q ?_
      intro g
      refine Quotient.inductionOn' r ?_
      intro h
      refine ⟨g⁻¹ * h, ?_⟩
      simp only [rightMul_mk, mul_inv_cancel_left]
    · intro g
      let q : RightCosets C := Quotient.mk'' g
      -- H is g⁻¹ C g, because conj g sends a to g*a*g⁻¹.
      let H := C.comap (MulAut.conj g).toMonoidHom
      have hfix (a : G) : rightMul C a q = q ↔ a ∈ H := by
        change Quotient.mk'' (g * a) = Quotient.mk'' g ↔ g * a * g⁻¹ ∈ C
        constructor
        · intro ha
          exact QuotientGroup.rightRel_apply.mp (Quotient.exact' ha.symm)
        · intro ha
          exact (Quotient.sound' (QuotientGroup.rightRel_apply.mpr ha)).symm
      have hmem (a : K.op) :
          a ∈ MulAction.stabilizer K.op q ↔ a.1.unop ∈ H := by
        change rightMul C a.1.unop q = q ↔ a.1.unop ∈ H
        exact hfix a.1.unop
      let e : MulAction.stabilizer K.op q ≃ H.subgroupOf K :=
        { toFun := fun a => ⟨⟨a.1.1.unop, a.1.2⟩, (hmem a.1).mp a.2⟩
          invFun := fun a =>
            ⟨⟨MulOpposite.op a.1.1, a.1.2⟩,
              (hmem ⟨MulOpposite.op a.1.1, a.1.2⟩).mpr a.2⟩
          left_inv := by
            intro a
            apply Subtype.ext
            apply Subtype.ext
            rfl
          right_inv := by
            intro a
            apply Subtype.ext
            apply Subtype.ext
            rfl }
      have hKcard : Nat.card K.op = Nat.card K :=
        (Nat.card_congr K.equivOp).symm
      have hScard :
          Nat.card (MulAction.stabilizer K.op q) = Nat.card (H.subgroupOf K) :=
        Nat.card_congr e
      have horbit :
          Set.range (fun a : K => rightMul C (a : G) q) = MulAction.orbit K.op q := by
        ext r
        constructor
        · rintro ⟨a, rfl⟩
          exact MulAction.mem_orbit_iff.mpr
            ⟨⟨MulOpposite.op (a : G), a.2⟩, rfl⟩
        · intro hr
          obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hr
          exact ⟨⟨a.1.unop, a.2⟩, ha⟩
      calc
        (Set.range (fun a : K => rightMul C (a : G) q)).ncard =
            (MulAction.orbit K.op q).ncard := congrArg Set.ncard horbit
        _ = (MulAction.stabilizer K.op q).index :=
          (MulAction.index_stabilizer K.op q).symm
        _ = (H.subgroupOf K).index := by
          rw [Subgroup.index_eq_card_div, Subgroup.index_eq_card_div, hKcard, hScard]
        _ = (K ⊓ H).relIndex K := by
          change H.relIndex K = (K ⊓ H).relIndex K
          exact (Subgroup.inf_relIndex_left K H).symm
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let whole ← Lean.Meta.getLocalDeclFromUserName `hwhole
      let some raw := whole.value? |
        Lean.throwError "AXIOMS64_ORBIT: hwhole must have a visible let value"
      let raw ← Lean.instantiateMVars raw
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let wholeType ← Lean.instantiateMVars whole.type
      if raw.hasMVar || target.hasMVar || wholeType.hasMVar then
        Lean.throwError "AXIOMS64_ORBIT: unresolved expression or universe metavariables"
      unless ← Lean.Meta.isDefEq wholeType target do
        Lean.throwError "AXIOMS64_ORBIT: hwhole type differs from the original conclusion"
      unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType raw) target do
        Lean.throwError "AXIOMS64_ORBIT: whole proof has the wrong conclusion"
      let originalNames : Array Lean.Name :=
        #[`G, `groupInst, `finiteInst, `u, `v, `_generates, `C]
      let mut params : Array Lean.Expr := #[]
      for originalName in originalNames do
        let decl ← Lean.Meta.getLocalDeclFromUserName originalName
        if (decl.value? (allowNondep := true)).isSome then
          Lean.throwError m!"AXIOMS64_ORBIT: original parameter is a local let: {originalName}"
        params := params.push (Lean.mkFVar decl.fvarId)
      unless params.size == 7 do
        Lean.throwError m!"AXIOMS64_ORBIT: expected original 7 parameters, got {params.size}"
      let proof ← Lean.instantiateMVars (← Lean.Meta.mkLambdaFVars params raw)
      let proofType ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
      let expectedType ← Lean.instantiateMVars (← Lean.Meta.mkForallFVars params target)
      if proof.hasMVar || proofType.hasMVar || expectedType.hasMVar then
        Lean.throwError "AXIOMS64_ORBIT: closed proof or type still has metavariables"
      if proof.hasFVar || proofType.hasFVar || expectedType.hasFVar then
        Lean.throwError "AXIOMS64_ORBIT: proof has assumptions beyond the original parameters"
      if proof.hasLooseBVars || proofType.hasLooseBVars || expectedType.hasLooseBVars then
        Lean.throwError "AXIOMS64_ORBIT: closed proof or type has loose bound variables"
      unless ← Lean.Meta.isDefEq proofType expectedType do
        Lean.throwError "AXIOMS64_ORBIT: closed proof does not have the original full telescope"
      let mut constants : Lean.NameSet := {}
      for constant in proof.getUsedConstants do
        constants := constants.insert constant
      for constant in proofType.getUsedConstants do
        constants := constants.insert constant
      let env := (← Lean.getEnv).setExporting false
      let mut axioms : Lean.NameSet := {}
      for constant in constants.toArray.qsort Lean.Name.lt do
        if (env.checked.get.find? constant).isNone then
          Lean.throwError m!"AXIOMS64_ORBIT: constant absent from checked environment: {constant}"
        for axiomName in ← Lean.collectAxioms constant do
          axioms := axioms.insert axiomName
      let axiomNames := axioms.toArray.qsort Lean.Name.lt
      let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
      for axiomName in axiomNames do
        unless allowed.contains axiomName do
          Lean.throwError m!"AXIOMS64_ORBIT: disallowed axiom dependency: {axiomName}"
      let names := String.intercalate ", " (axiomNames.toList.map toString)
      Lean.logInfo m!"CFMP_RIGHT_COSET1222_ORBIT_AXIOMS64 exact_axioms=[{names}] constant_count={constants.toArray.size} original_parameter_count={params.size}"
  exact hwhole

end
end

section
open D5.S3.FiniteGroups.CFMPNormalizerCentralizer
open D5.S3.Geometry.Gluing.ActualCornerPointPeriods

noncomputable section
set_option autoImplicit false

-- Transient exact application on the same right-coset action.
-- The two low rows and two high rows retain their original ordered-corner meanings.
example {G : Type*} [groupInst : Group G] [finiteInst : Finite G] (u v : G)
    (_generates : Subgroup.closure ({u, v} : Set G) = ⊤) (C : Subgroup G)
    (hCell : ∀ g : G, Disjoint C
      ((Subgroup.zpowers (v⁻¹ * u ^ 2)).map (MulAut.conj g).toMonoidHom))
    (hCh : ∀ g : G, Disjoint C
      ((Subgroup.zpowers (v ^ 2 * u)).map (MulAut.conj g).toMonoidHom)) :
  letI : MulAction Gᵐᵒᵖ (RightCosets C) where
    smul a q := rightMul C a.unop q
    one_smul q := by
      refine Quotient.inductionOn' q ?_
      intro g
      change Quotient.mk'' (g * (1 : G)) = Quotient.mk'' g
      simp
    mul_smul a b q := by
      refine Quotient.inductionOn' q ?_
      intro g
      change Quotient.mk'' (g * (b.unop * a.unop)) =
        Quotient.mk'' ((g * b.unop) * a.unop)
      congr 1
      exact (mul_assoc g b.unop a.unop).symm
  (let ell := v⁻¹ * u ^ 2
  let h := v ^ 2 * u
  let s := (u ^ 2)⁻¹ * v
  let t := (u ^ 3)⁻¹ * v * u
  let k := v * u ^ 3
  ∀ q : RightCosets C,
    Function.minimalPeriod (rightMul C ell) q = orderOf ell ∧
    Function.minimalPeriod (rightMul C h) q = orderOf h ∧
    Function.minimalPeriod (rightMul C s⁻¹) q = orderOf ell ∧
    Function.minimalPeriod (rightMul C (s * k)) q = orderOf h ∧
    Function.minimalPeriod (rightMul C t) q = orderOf ell ∧
    Function.minimalPeriod (rightMul C (k * t)⁻¹) q = orderOf h) ∧
  ∀ (q : RightCosets C) (c : Fin 4),
    pointPeriod u v c q =
      (if c.val < 2 then orderOf (v⁻¹ * u ^ 2) else orderOf (v ^ 2 * u)) ∧
    Function.minimalPeriod (tour u v c) (q, 0) =
      3 * (if c.val < 2 then orderOf (v⁻¹ * u ^ 2) else orderOf (v ^ 2 * u)) := by
  let hwhole :
    letI : MulAction Gᵐᵒᵖ (RightCosets C) where
      smul a q := rightMul C a.unop q
      one_smul q := by
        refine Quotient.inductionOn' q ?_
        intro g
        change Quotient.mk'' (g * (1 : G)) = Quotient.mk'' g
        simp
      mul_smul a b q := by
        refine Quotient.inductionOn' q ?_
        intro g
        change Quotient.mk'' (g * (b.unop * a.unop)) =
          Quotient.mk'' ((g * b.unop) * a.unop)
        congr 1
        exact (mul_assoc g b.unop a.unop).symm
    (let ell := v⁻¹ * u ^ 2
    let h := v ^ 2 * u
    let s := (u ^ 2)⁻¹ * v
    let t := (u ^ 3)⁻¹ * v * u
    let k := v * u ^ 3
    ∀ q : RightCosets C,
      Function.minimalPeriod (rightMul C ell) q = orderOf ell ∧
      Function.minimalPeriod (rightMul C h) q = orderOf h ∧
      Function.minimalPeriod (rightMul C s⁻¹) q = orderOf ell ∧
      Function.minimalPeriod (rightMul C (s * k)) q = orderOf h ∧
      Function.minimalPeriod (rightMul C t) q = orderOf ell ∧
      Function.minimalPeriod (rightMul C (k * t)⁻¹) q = orderOf h) ∧
    ∀ (q : RightCosets C) (c : Fin 4),
      pointPeriod u v c q =
        (if c.val < 2 then orderOf (v⁻¹ * u ^ 2) else orderOf (v ^ 2 * u)) ∧
      Function.minimalPeriod (tour u v c) (q, 0) =
        3 * (if c.val < 2 then orderOf (v⁻¹ * u ^ 2) else orderOf (v ^ 2 * u)) := by
    letI : MulAction Gᵐᵒᵖ (RightCosets C) where
      smul a q := rightMul C a.unop q
      one_smul q := by
        refine Quotient.inductionOn' q ?_
        intro g
        change Quotient.mk'' (g * (1 : G)) = Quotient.mk'' g
        simp
      mul_smul a b q := by
        refine Quotient.inductionOn' q ?_
        intro g
        change Quotient.mk'' (g * (b.unop * a.unop)) =
          Quotient.mk'' ((g * b.unop) * a.unop)
        congr 1
        exact (mul_assoc g b.unop a.unop).symm
    have hperiods :
        let ell := v⁻¹ * u ^ 2
        let h := v ^ 2 * u
        let s := (u ^ 2)⁻¹ * v
        let t := (u ^ 3)⁻¹ * v * u
        let k := v * u ^ 3
        ∀ q : RightCosets C,
          Function.minimalPeriod (rightMul C ell) q = orderOf ell ∧
          Function.minimalPeriod (rightMul C h) q = orderOf h ∧
          Function.minimalPeriod (rightMul C s⁻¹) q = orderOf ell ∧
          Function.minimalPeriod (rightMul C (s * k)) q = orderOf h ∧
          Function.minimalPeriod (rightMul C t) q = orderOf ell ∧
          Function.minimalPeriod (rightMul C (k * t)⁻¹) q = orderOf h := by
      let ell := v⁻¹ * u ^ 2
      let h := v ^ 2 * u
      let s := (u ^ 2)⁻¹ * v
      let t := (u ^ 3)⁻¹ * v * u
      let k := v * u ^ 3
      change ∀ q : RightCosets C,
        Function.minimalPeriod (rightMul C ell) q = orderOf ell ∧
        Function.minimalPeriod (rightMul C h) q = orderOf h ∧
        Function.minimalPeriod (rightMul C s⁻¹) q = orderOf ell ∧
        Function.minimalPeriod (rightMul C (s * k)) q = orderOf h ∧
        Function.minimalPeriod (rightMul C t) q = orderOf ell ∧
        Function.minimalPeriod (rightMul C (k * t)⁻¹) q = orderOf h
      letI : MulAction Gᵐᵒᵖ (RightCosets C) where
        smul a q := rightMul C a.unop q
        one_smul q := by
          refine Quotient.inductionOn' q ?_
          intro g
          change Quotient.mk'' (g * (1 : G)) = Quotient.mk'' g
          simp
        mul_smul a b q := by
          refine Quotient.inductionOn' q ?_
          intro g
          change Quotient.mk'' (g * (b.unop * a.unop)) =
            Quotient.mk'' ((g * b.unop) * a.unop)
          congr 1
          exact (mul_assoc g b.unop a.unop).symm
      have hperiod (x : G)
          (hx : ∀ g : G, Disjoint C
            ((Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom))
          (q : RightCosets C) :
          Function.minimalPeriod (rightMul C x) q = orderOf x := by
        change MulAction.period (MulOpposite.op x) q = orderOf x
        refine Quotient.inductionOn' q ?_
        intro g
        let qg : RightCosets C := Quotient.mk'' g
        let n := MulAction.period (MulOpposite.op x) qg
        have hfix : rightMul C (x ^ n) qg = qg :=
          MulAction.pow_period_smul (MulOpposite.op x) qg
        have hCmem : g * x ^ n * g⁻¹ ∈ C :=
          QuotientGroup.rightRel_apply.mp (Quotient.exact' hfix.symm)
        have hZmem : g * x ^ n * g⁻¹ ∈
            (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨x ^ n, Subgroup.npow_mem_zpowers x n, rfl⟩
        have hconj : g * x ^ n * g⁻¹ = 1 :=
          Subgroup.disjoint_def.mp (hx g) hCmem hZmem
        have hpow : x ^ n = 1 := by
          apply (MulAut.conj g).injective
          simpa using hconj
        have hopOrder : orderOf (MulOpposite.op x) = orderOf x := by
          apply orderOf_eq_orderOf_iff.mpr
          intro m
          change MulOpposite.op (x ^ m) = MulOpposite.op (1 : G) ↔ x ^ m = 1
          exact MulOpposite.op_inj
        apply Nat.dvd_antisymm
        · simpa only [hopOrder] using
            MulAction.period_dvd_orderOf (MulOpposite.op x) qg
        · exact orderOf_dvd_iff_pow_eq_one.mpr hpow
      have hinv (x : G)
          (hx : ∀ g : G, Disjoint C
            ((Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom)) :
          ∀ g : G, Disjoint C
            ((Subgroup.zpowers x⁻¹).map (MulAut.conj g).toMonoidHom) := by
        intro g
        simpa only [Subgroup.zpowers_inv] using hx g
      have hconj (x a : G)
          (hx : ∀ g : G, Disjoint C
            ((Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom)) :
          ∀ g : G, Disjoint C
            ((Subgroup.zpowers ((MulAut.conj a) x)).map
              (MulAut.conj g).toMonoidHom) := by
        intro g
        have hmap :
            (MulAut.conj g).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
            (MulAut.conj (g * a)).toMonoidHom := by
          ext z
          simp [MulAut.conj_apply, mul_inv_rev, mul_assoc]
        rw [← (MulAut.conj a).toMonoidHom.map_zpowers x, Subgroup.map_map, hmap]
        exact hx (g * a)
      have hc1 : s⁻¹ = ell := by
        dsimp [s, ell]
        group
      have hc2 : s * k = (MulAut.conj ((u ^ 2)⁻¹)) h := by
        dsimp [s, k, h]
        simp only [MulAut.conj_apply]
        group
      have hc3 : t = (MulAut.conj u⁻¹) ell⁻¹ := by
        dsimp [t, ell]
        simp only [MulAut.conj_apply]
        group
      have hc4 : (k * t)⁻¹ = h⁻¹ := by
        dsimp [k, t, h]
        group
      intro q
      refine ⟨hperiod ell hCell q, hperiod h hCh q, ?_, ?_, ?_, ?_⟩
      · simpa only [hc1] using hperiod ell hCell q
      · rw [hc2]
        exact (hperiod ((MulAut.conj ((u ^ 2)⁻¹)) h)
          (hconj h ((u ^ 2)⁻¹) hCh) q).trans
          ((MulAut.conj ((u ^ 2)⁻¹)).orderOf_eq h)
      · rw [hc3]
        exact (hperiod ((MulAut.conj u⁻¹) ell⁻¹)
          (hconj ell⁻¹ u⁻¹ (hinv ell hCell)) q).trans
          (((MulAut.conj u⁻¹).orderOf_eq ell⁻¹).trans (orderOf_inv ell))
      · rw [hc4]
        exact (hperiod h⁻¹ (hinv h hCh) q).trans (orderOf_inv h)
    change (let ell := v⁻¹ * u ^ 2
    let h := v ^ 2 * u
    let s := (u ^ 2)⁻¹ * v
    let t := (u ^ 3)⁻¹ * v * u
    let k := v * u ^ 3
    ∀ q : RightCosets C,
      Function.minimalPeriod (rightMul C ell) q = orderOf ell ∧
      Function.minimalPeriod (rightMul C h) q = orderOf h ∧
      Function.minimalPeriod (rightMul C s⁻¹) q = orderOf ell ∧
      Function.minimalPeriod (rightMul C (s * k)) q = orderOf h ∧
      Function.minimalPeriod (rightMul C t) q = orderOf ell ∧
      Function.minimalPeriod (rightMul C (k * t)⁻¹) q = orderOf h) ∧
    ∀ (q : RightCosets C) (c : Fin 4),
      pointPeriod u v c q =
        (if c.val < 2 then orderOf (v⁻¹ * u ^ 2) else orderOf (v ^ 2 * u)) ∧
      Function.minimalPeriod (tour u v c) (q, 0) =
        3 * (if c.val < 2 then orderOf (v⁻¹ * u ^ 2) else orderOf (v ^ 2 * u))
    refine ⟨hperiods, ?_⟩
    intro q c
    have hrow : pointPeriod u v c q =
        (if c.val < 2 then orderOf (v⁻¹ * u ^ 2) else orderOf (v ^ 2 * u)) := by
      fin_cases c
      · change Function.minimalPeriod (rightMul C (v⁻¹ * u ^ 2)) q =
          orderOf (v⁻¹ * u ^ 2)
        exact (hperiods q).1
      · change Function.minimalPeriod (rightMul C (v⁻¹ * u ^ 2)) q =
          orderOf (v⁻¹ * u ^ 2)
        exact (hperiods q).1
      · change Function.minimalPeriod (rightMul C (v ^ 2 * u)) q = orderOf (v ^ 2 * u)
        exact (hperiods q).2.1
      · change Function.minimalPeriod (rightMul C (v ^ 2 * u)) q = orderOf (v ^ 2 * u)
        exact (hperiods q).2.1
    have htour : Function.minimalPeriod (tour u v c) (q, 0) =
        3 * pointPeriod u v c q :=
      (actual_component_enumeration u v c q).2.2.2.2.2.1
    exact ⟨hrow, htour.trans (congrArg (fun n : ℕ => 3 * n) hrow)⟩
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let whole ← Lean.Meta.getLocalDeclFromUserName `hwhole
      let some raw := whole.value? |
        Lean.throwError "AXIOMS67_POINT_PERIODS: hwhole must have a visible let value"
      let raw ← Lean.instantiateMVars raw
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let wholeType ← Lean.instantiateMVars whole.type
      if raw.hasMVar || target.hasMVar || wholeType.hasMVar then
        Lean.throwError "AXIOMS67_POINT_PERIODS: unresolved expression or universe metavariables"
      unless ← Lean.Meta.isDefEq wholeType target do
        Lean.throwError "AXIOMS67_POINT_PERIODS: hwhole type differs from the original conclusion"
      unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType raw) target do
        Lean.throwError "AXIOMS67_POINT_PERIODS: whole proof has the wrong conclusion"
      let originalNames : Array Lean.Name :=
        #[`G, `groupInst, `finiteInst, `u, `v, `_generates, `C, `hCell, `hCh]
      let mut params : Array Lean.Expr := #[]
      for originalName in originalNames do
        let decl ← Lean.Meta.getLocalDeclFromUserName originalName
        if (decl.value? (allowNondep := true)).isSome then
          Lean.throwError m!"AXIOMS67_POINT_PERIODS: original parameter is a local let: {originalName}"
        params := params.push (Lean.mkFVar decl.fvarId)
      unless params.size == 9 do
        Lean.throwError m!"AXIOMS67_POINT_PERIODS: expected original 9 parameters, got {params.size}"
      let proof ← Lean.instantiateMVars (← Lean.Meta.mkLambdaFVars params raw)
      let proofType ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
      let expectedType ← Lean.instantiateMVars (← Lean.Meta.mkForallFVars params target)
      if proof.hasMVar || proofType.hasMVar || expectedType.hasMVar then
        Lean.throwError "AXIOMS67_POINT_PERIODS: closed proof or type still has metavariables"
      if proof.hasFVar || proofType.hasFVar || expectedType.hasFVar then
        Lean.throwError "AXIOMS67_POINT_PERIODS: proof has assumptions beyond the original parameters"
      if proof.hasLooseBVars || proofType.hasLooseBVars || expectedType.hasLooseBVars then
        Lean.throwError "AXIOMS67_POINT_PERIODS: closed proof or type has loose bound variables"
      unless ← Lean.Meta.isDefEq proofType expectedType do
        Lean.throwError "AXIOMS67_POINT_PERIODS: closed proof does not have the original full telescope"
      let mut constants : Lean.NameSet := {}
      for constant in proof.getUsedConstants do
        constants := constants.insert constant
      for constant in proofType.getUsedConstants do
        constants := constants.insert constant
      let env := (← Lean.getEnv).setExporting false
      let mut axioms : Lean.NameSet := {}
      for constant in constants.toArray.qsort Lean.Name.lt do
        if (env.checked.get.find? constant).isNone then
          Lean.throwError m!"AXIOMS67_POINT_PERIODS: constant absent from checked environment: {constant}"
        for axiomName in ← Lean.collectAxioms constant do
          axioms := axioms.insert axiomName
      let axiomNames := axioms.toArray.qsort Lean.Name.lt
      let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
      for axiomName in axiomNames do
        unless allowed.contains axiomName do
          Lean.throwError m!"AXIOMS67_POINT_PERIODS: disallowed axiom dependency: {axiomName}"
      let names := String.intercalate ", " (axiomNames.toList.map toString)
      Lean.logInfo m!"CFMP_RIGHT_COSET1222_POINT_PERIODS_AXIOMS67 exact_axioms=[{names}] constant_count={constants.toArray.size} original_parameter_count={params.size}"
  exact hwhole

end
end

section
open D5.S3.FiniteGroups.CFMPNormalizerCentralizer

noncomputable section
set_option autoImplicit false

-- The component relation is the existing double-coset relation.
example {G : Type*} [groupInst : Group G] [finiteInst : Finite G] (u v : G)
    (_generates : Subgroup.closure ({u, v} : Set G) = ⊤) (C : Subgroup G)
    (g h : G) :
    let K := Subgroup.closure
      ({(u ^ 2)⁻¹ * v, (u ^ 3)⁻¹ * v * u, v * u ^ 3} : Set G)
    (∃ a ∈ K,
      rightMul C a (Quotient.mk'' g : RightCosets C) = Quotient.mk'' h) ↔
      DoubleCoset.setoid (C : Set G) (K : Set G) g h := by
  let hwhole :
      let K := Subgroup.closure
        ({(u ^ 2)⁻¹ * v, (u ^ 3)⁻¹ * v * u, v * u ^ 3} : Set G)
      (∃ a ∈ K,
        rightMul C a (Quotient.mk'' g : RightCosets C) = Quotient.mk'' h) ↔
        DoubleCoset.setoid (C : Set G) (K : Set G) g h := by
    let K := Subgroup.closure
      ({(u ^ 2)⁻¹ * v, (u ^ 3)⁻¹ * v * u, v * u ^ 3} : Set G)
    change (∃ a ∈ K,
      rightMul C a (Quotient.mk'' g : RightCosets C) = Quotient.mk'' h) ↔
      DoubleCoset.setoid (C : Set G) (K : Set G) g h
    rw [DoubleCoset.rel_iff]
    constructor
    · rintro ⟨a, ha, heq⟩
      have hCmem : h * (g * a)⁻¹ ∈ C :=
        QuotientGroup.rightRel_apply.mp (Quotient.exact' heq)
      refine ⟨h * (g * a)⁻¹, hCmem, a, ha, ?_⟩
      group
    · rintro ⟨c, hc, a, ha, rfl⟩
      refine ⟨a, ha, ?_⟩
      apply Quotient.sound'
      apply QuotientGroup.rightRel_apply.mpr
      simpa [mul_inv_rev, mul_assoc] using hc
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let whole ← Lean.Meta.getLocalDeclFromUserName `hwhole
      let some raw := whole.value? |
        Lean.throwError "AXIOMS64_DOUBLE_COSET: hwhole must have a visible let value"
      let raw ← Lean.instantiateMVars raw
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let wholeType ← Lean.instantiateMVars whole.type
      if raw.hasMVar || target.hasMVar || wholeType.hasMVar then
        Lean.throwError "AXIOMS64_DOUBLE_COSET: unresolved expression or universe metavariables"
      unless ← Lean.Meta.isDefEq wholeType target do
        Lean.throwError "AXIOMS64_DOUBLE_COSET: hwhole type differs from the original conclusion"
      unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType raw) target do
        Lean.throwError "AXIOMS64_DOUBLE_COSET: whole proof has the wrong conclusion"
      let originalNames : Array Lean.Name :=
        #[`G, `groupInst, `finiteInst, `u, `v, `_generates, `C, `g, `h]
      let mut params : Array Lean.Expr := #[]
      for originalName in originalNames do
        let decl ← Lean.Meta.getLocalDeclFromUserName originalName
        if (decl.value? (allowNondep := true)).isSome then
          Lean.throwError m!"AXIOMS64_DOUBLE_COSET: original parameter is a local let: {originalName}"
        params := params.push (Lean.mkFVar decl.fvarId)
      unless params.size == 9 do
        Lean.throwError m!"AXIOMS64_DOUBLE_COSET: expected original 9 parameters, got {params.size}"
      let proof ← Lean.instantiateMVars (← Lean.Meta.mkLambdaFVars params raw)
      let proofType ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
      let expectedType ← Lean.instantiateMVars (← Lean.Meta.mkForallFVars params target)
      if proof.hasMVar || proofType.hasMVar || expectedType.hasMVar then
        Lean.throwError "AXIOMS64_DOUBLE_COSET: closed proof or type still has metavariables"
      if proof.hasFVar || proofType.hasFVar || expectedType.hasFVar then
        Lean.throwError "AXIOMS64_DOUBLE_COSET: proof has assumptions beyond the original parameters"
      if proof.hasLooseBVars || proofType.hasLooseBVars || expectedType.hasLooseBVars then
        Lean.throwError "AXIOMS64_DOUBLE_COSET: closed proof or type has loose bound variables"
      unless ← Lean.Meta.isDefEq proofType expectedType do
        Lean.throwError "AXIOMS64_DOUBLE_COSET: closed proof does not have the original full telescope"
      let mut constants : Lean.NameSet := {}
      for constant in proof.getUsedConstants do
        constants := constants.insert constant
      for constant in proofType.getUsedConstants do
        constants := constants.insert constant
      let env := (← Lean.getEnv).setExporting false
      let mut axioms : Lean.NameSet := {}
      for constant in constants.toArray.qsort Lean.Name.lt do
        if (env.checked.get.find? constant).isNone then
          Lean.throwError m!"AXIOMS64_DOUBLE_COSET: constant absent from checked environment: {constant}"
        for axiomName in ← Lean.collectAxioms constant do
          axioms := axioms.insert axiomName
      let axiomNames := axioms.toArray.qsort Lean.Name.lt
      let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
      for axiomName in axiomNames do
        unless allowed.contains axiomName do
          Lean.throwError m!"AXIOMS64_DOUBLE_COSET: disallowed axiom dependency: {axiomName}"
      let names := String.intercalate ", " (axiomNames.toList.map toString)
      Lean.logInfo m!"CFMP_RIGHT_COSET1222_DOUBLE_COSET_AXIOMS64 exact_axioms=[{names}] constant_count={constants.toArray.size} original_parameter_count={params.size}"
  exact hwhole

end
end

section
open D5.S3.FiniteGroups.CFMPNormalizerCentralizer
open D5.S3.Geometry.Hyperideal.ActualCornerTransport
open D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits

noncomputable section
set_option autoImplicit false

-- Transient exact application candidate; no compilation or canonical retention.
example {G : Type*} [groupInst : Group G] [finiteInst : Finite G] (u v : G)
    (_generates : Subgroup.closure ({u, v} : Set G) = ⊤) (C : Subgroup G) :
  letI : MulAction Gᵐᵒᵖ (RightCosets C) where
    smul a q := rightMul C a.unop q
    one_smul q := by
      refine Quotient.inductionOn' q ?_
      intro g
      change Quotient.mk'' (g * (1 : G)) = Quotient.mk'' g
      simp
    mul_smul a b q := by
      refine Quotient.inductionOn' q ?_
      intro g
      change Quotient.mk'' (g * (b.unop * a.unop)) =
        Quotient.mk'' ((g * b.unop) * a.unop)
      congr 1
      exact (mul_assoc g b.unop a.unop).symm
  ∀ (g h : G) (i j : Fin 4),
    Relation.EqvGen (cornerRel (pairing u v))
      ((Quotient.mk'' g : RightCosets C), i)
      ((Quotient.mk'' h : RightCosets C), j) ↔
    DoubleCoset.setoid (C : Set G) (boundaryGroup u v : Set G)
      (g * u ^ i.val) (h * u ^ j.val) := by
  let hwhole :
    letI : MulAction Gᵐᵒᵖ (RightCosets C) where
      smul a q := rightMul C a.unop q
      one_smul q := by
        refine Quotient.inductionOn' q ?_
        intro g
        change Quotient.mk'' (g * (1 : G)) = Quotient.mk'' g
        simp
      mul_smul a b q := by
        refine Quotient.inductionOn' q ?_
        intro g
        change Quotient.mk'' (g * (b.unop * a.unop)) =
          Quotient.mk'' ((g * b.unop) * a.unop)
        congr 1
        exact (mul_assoc g b.unop a.unop).symm
    ∀ (g h : G) (i j : Fin 4),
      Relation.EqvGen (cornerRel (pairing u v))
        ((Quotient.mk'' g : RightCosets C), i)
        ((Quotient.mk'' h : RightCosets C), j) ↔
      DoubleCoset.setoid (C : Set G) (boundaryGroup u v : Set G)
        (g * u ^ i.val) (h * u ^ j.val) := by
    letI : MulAction Gᵐᵒᵖ (RightCosets C) where
      smul a q := rightMul C a.unop q
      one_smul q := by
        refine Quotient.inductionOn' q ?_
        intro g
        change Quotient.mk'' (g * (1 : G)) = Quotient.mk'' g
        simp
      mul_smul a b q := by
        refine Quotient.inductionOn' q ?_
        intro g
        change Quotient.mk'' (g * (b.unop * a.unop)) =
          Quotient.mk'' ((g * b.unop) * a.unop)
        congr 1
        exact (mul_assoc g b.unop a.unop).symm
    change ∀ (g h : G) (i j : Fin 4),
      Relation.EqvGen (cornerRel (pairing u v))
        ((Quotient.mk'' g : RightCosets C), i)
        ((Quotient.mk'' h : RightCosets C), j) ↔
      DoubleCoset.setoid (C : Set G) (boundaryGroup u v : Set G)
        (g * u ^ i.val) (h * u ^ j.val)
    have hdouble (g h : G) :
        (∃ a ∈ boundaryGroup u v,
          rightMul C a (Quotient.mk'' g : RightCosets C) = Quotient.mk'' h) ↔
        DoubleCoset.setoid (C : Set G) (boundaryGroup u v : Set G) g h := by
      rw [DoubleCoset.rel_iff]
      constructor
      · rintro ⟨a, ha, heq⟩
        have hCmem : h * (g * a)⁻¹ ∈ C :=
          QuotientGroup.rightRel_apply.mp (Quotient.exact' heq)
        refine ⟨h * (g * a)⁻¹, hCmem, a, ha, ?_⟩
        group
      · rintro ⟨c, hc, a, ha, rfl⟩
        refine ⟨a, ha, ?_⟩
        apply Quotient.sound'
        apply QuotientGroup.rightRel_apply.mpr
        simpa [mul_inv_rev, mul_assoc] using hc
    intro g h i j
    rw [actual_corner_orbit_iff]
    change (∃ a ∈ boundaryGroup u v,
      rightMul C a (Quotient.mk'' (g * u ^ i.val) : RightCosets C) =
        Quotient.mk'' (h * u ^ j.val)) ↔ _
    exact hdouble (g * u ^ i.val) (h * u ^ j.val)
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let whole ← Lean.Meta.getLocalDeclFromUserName `hwhole
      let some raw := whole.value? |
        Lean.throwError "AXIOMS64_ACTUAL_CORNERS: hwhole must have a visible let value"
      let raw ← Lean.instantiateMVars raw
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let wholeType ← Lean.instantiateMVars whole.type
      if raw.hasMVar || target.hasMVar || wholeType.hasMVar then
        Lean.throwError "AXIOMS64_ACTUAL_CORNERS: unresolved expression or universe metavariables"
      unless ← Lean.Meta.isDefEq wholeType target do
        Lean.throwError "AXIOMS64_ACTUAL_CORNERS: hwhole type differs from the original conclusion"
      unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType raw) target do
        Lean.throwError "AXIOMS64_ACTUAL_CORNERS: whole proof has the wrong conclusion"
      let originalNames : Array Lean.Name :=
        #[`G, `groupInst, `finiteInst, `u, `v, `_generates, `C]
      let mut params : Array Lean.Expr := #[]
      for originalName in originalNames do
        let decl ← Lean.Meta.getLocalDeclFromUserName originalName
        if (decl.value? (allowNondep := true)).isSome then
          Lean.throwError m!"AXIOMS64_ACTUAL_CORNERS: original parameter is a local let: {originalName}"
        params := params.push (Lean.mkFVar decl.fvarId)
      unless params.size == 7 do
        Lean.throwError m!"AXIOMS64_ACTUAL_CORNERS: expected original 7 parameters, got {params.size}"
      let proof ← Lean.instantiateMVars (← Lean.Meta.mkLambdaFVars params raw)
      let proofType ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
      let expectedType ← Lean.instantiateMVars (← Lean.Meta.mkForallFVars params target)
      if proof.hasMVar || proofType.hasMVar || expectedType.hasMVar then
        Lean.throwError "AXIOMS64_ACTUAL_CORNERS: closed proof or type still has metavariables"
      if proof.hasFVar || proofType.hasFVar || expectedType.hasFVar then
        Lean.throwError "AXIOMS64_ACTUAL_CORNERS: proof has assumptions beyond the original parameters"
      if proof.hasLooseBVars || proofType.hasLooseBVars || expectedType.hasLooseBVars then
        Lean.throwError "AXIOMS64_ACTUAL_CORNERS: closed proof or type has loose bound variables"
      unless ← Lean.Meta.isDefEq proofType expectedType do
        Lean.throwError "AXIOMS64_ACTUAL_CORNERS: closed proof does not have the original full telescope"
      let mut constants : Lean.NameSet := {}
      for constant in proof.getUsedConstants do
        constants := constants.insert constant
      for constant in proofType.getUsedConstants do
        constants := constants.insert constant
      let env := (← Lean.getEnv).setExporting false
      let mut axioms : Lean.NameSet := {}
      for constant in constants.toArray.qsort Lean.Name.lt do
        if (env.checked.get.find? constant).isNone then
          Lean.throwError m!"AXIOMS64_ACTUAL_CORNERS: constant absent from checked environment: {constant}"
        for axiomName in ← Lean.collectAxioms constant do
          axioms := axioms.insert axiomName
      let axiomNames := axioms.toArray.qsort Lean.Name.lt
      let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
      for axiomName in axiomNames do
        unless allowed.contains axiomName do
          Lean.throwError m!"AXIOMS64_ACTUAL_CORNERS: disallowed axiom dependency: {axiomName}"
      let names := String.intercalate ", " (axiomNames.toList.map toString)
      Lean.logInfo m!"CFMP_RIGHT_COSET1222_ACTUAL_CORNERS_AXIOMS64 exact_axioms=[{names}] constant_count={constants.toArray.size} original_parameter_count={params.size}"
  exact hwhole

end
end
