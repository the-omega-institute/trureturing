import D5.S3.Geometry.Hyperideal.ReturnCycleWords
import Mathlib.Algebra.Group.Action.End
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Util.CollectAxioms

/- Transient anonymous application candidate. This file has not been compiled. -/

noncomputable section

open D5.S3.Geometry.Hyperideal.ActualCornerTransport
open D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits
open D5.S3.Geometry.Hyperideal.ReturnCycleWords

example {G Ω : Type*} [groupInst : Group G]
    [actionInst : MulAction Gᵐᵒᵖ Ω] [finiteInst : Finite Ω]
    (u v : G) (high : Bool) (x : Ω) :
    let period := Function.minimalPeriod (fun y : Ω => act y (returnWord u v high)) x
    let Fibre := {a : Occurrence Ω //
      P (pairing u v) (x, baseEdge high) = P (pairing u v) a}
    let position : Fin 3 → Fin 6 := if high then ![1, 2, 4] else ![0, 3, 5]
    let middle : Fin 6 := if high then 2 else 5
    0 < period ∧
      Nat.card Fibre = 3 * period ∧
      (∀ s : Fin 3, Nat.card {a : Fibre // a.val.2 = position s} = period) ∧
      Nat.card {a : Fibre // a.val.2 = middle} = period ∧
      Nat.card {a : Fibre // a.val.2 ≠ middle} = 2 * period ∧
      Nat.card {a : Fibre // a.val.2 ≠ middle} =
        2 * Nat.card {a : Fibre // a.val.2 = middle} := by
  let hwhole :
      let period := Function.minimalPeriod (fun y : Ω => act y (returnWord u v high)) x
      let Fibre := {a : Occurrence Ω //
        P (pairing u v) (x, baseEdge high) = P (pairing u v) a}
      let position : Fin 3 → Fin 6 := if high then ![1, 2, 4] else ![0, 3, 5]
      let middle : Fin 6 := if high then 2 else 5
      0 < period ∧
        Nat.card Fibre = 3 * period ∧
        (∀ s : Fin 3, Nat.card {a : Fibre // a.val.2 = position s} = period) ∧
        Nat.card {a : Fibre // a.val.2 = middle} = period ∧
        Nat.card {a : Fibre // a.val.2 ≠ middle} = 2 * period ∧
        Nat.card {a : Fibre // a.val.2 ≠ middle} =
          2 * Nat.card {a : Fibre // a.val.2 = middle} := by
    classical
    letI := Fintype.ofFinite Ω
    let w := returnWord u v high
    let f : Ω → Ω := fun y => act y w
    let period := Function.minimalPeriod f x
    let Fibre := {a : Occurrence Ω //
      P (pairing u v) (x, baseEdge high) = P (pairing u v) a}
    let position : Fin 3 → Fin 6 := if high then ![1, 2, 4] else ![0, 3, 5]
    let phase : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]
    let offset : Fin 6 → G := ![1, 1, v * u, u ^ 2, u, u]
    let middle : Fin 6 := if high then 2 else 5
    change 0 < period ∧ Nat.card Fibre = 3 * period ∧
      (∀ s : Fin 3, Nat.card {a : Fibre // a.val.2 = position s} = period) ∧
      Nat.card {a : Fibre // a.val.2 = middle} = period ∧
      Nat.card {a : Fibre // a.val.2 ≠ middle} = 2 * period ∧
      Nat.card {a : Fibre // a.val.2 ≠ middle} =
        2 * Nat.card {a : Fibre // a.val.2 = middle}
    have hphase (s : Fin 3) : phase (position s) = s := by
      cases high <;> fin_cases s <;> rfl
    have hfamily (s : Fin 3) : family (position s) = high := by
      cases high <;> fin_cases s <;> rfl
    have hposition (j : Fin 6) (hj : family j = high) : position (phase j) = j := by
      cases high <;> fin_cases j <;> simp_all [family, position, phase]
    have hposition_inj : Function.Injective position := by
      intro a b hab
      simpa only [hphase] using congrArg phase hab
    let perm : Equiv.Perm Ω :=
      MulAction.toPermHom Gᵐᵒᵖ Ω (MulOpposite.op w)
    have hperm : (perm : Ω → Ω) = f := rfl
    have hperiodic : x ∈ Function.periodicPts f := by
      exact (show Function.Injective f from hperm ▸ perm.injective).mem_periodicPts x
    have hpositive : 0 < period :=
      Function.minimalPeriod_pos_of_mem_periodicPts hperiodic
    have hiterate (n : ℕ) : f^[n] x = act x (w ^ n) := by
      simpa only [f, act, MulOpposite.op_pow] using
        (smul_iterate_apply (MulOpposite.op w) n x)
    have hzpow (n : ℤ) : (perm ^ n) x = act x (w ^ n) := by
      change ((MulAction.toPermHom Gᵐᵒᵖ Ω (MulOpposite.op w)) ^ n) x = _
      rw [← map_zpow]
      rfl
    have hcyclic (y : Ω) :
        (∃ g ∈ returnGroup u v high, act x g = y) ↔
        ∃ n : Fin period, f^[n.val] x = y := by
      constructor
      · rintro ⟨g, hg, hxy⟩
        obtain ⟨k, hk⟩ := Subgroup.mem_closure_singleton.mp hg
        have hc : perm.SameCycle x y := by
          refine ⟨k, ?_⟩
          rw [hzpow, hk]
          exact hxy
        obtain ⟨n, hn⟩ := hc.exists_nat_pow_eq
        have hn' : f^[n] x = y := by
          simpa only [← Equiv.Perm.iterate_eq_pow, hperm] using hn
        refine ⟨⟨n % period, Nat.mod_lt _ hpositive⟩, ?_⟩
        exact (Function.iterate_mod_minimalPeriod_eq (f := f) (x := x) (n := n)).trans hn'
      · rintro ⟨n, hn⟩
        refine ⟨w ^ (n.val : ℤ), ?_, ?_⟩
        · exact Subgroup.mem_closure_singleton.mpr ⟨(n.val : ℤ), rfl⟩
        · simpa only [zpow_natCast, ← hiterate] using hn
    have hfibre (a : Occurrence Ω) :
        P (pairing u v) (x, baseEdge high) = P (pairing u v) a ↔
        family a.2 = high ∧ ∃ n : Fin period, f^[n.val] x = normalizeEdge u v a := by
      have hactual :
          P (pairing u v) (x, baseEdge high) = P (pairing u v) a ↔
          edgeClass u v (x, baseEdge high) a :=
        ⟨Quotient.exact, fun h =>
          Quotient.sound (s := Relation.EqvGen.setoid (edgeRel (pairing u v))) h⟩
      have hb : family (baseEdge high) = high := by
        cases high <;> rfl
      have hn : normalizeEdge u v (x, baseEdge high) = x := by
        cases high <;> simp [baseEdge, normalizeEdge]
      rw [hactual, actual_edge_orbit_iff, hb, hn, hcyclic]
      exact and_congr eq_comm Iff.rfl
    let encode : Fin 3 × Fin period → Occurrence Ω := fun q =>
      (act (f^[q.2.val] x) (offset (position q.1))⁻¹, position q.1)
    have hencode (q : Fin 3 × Fin period) :
        normalizeEdge u v (encode q) = f^[q.2.val] x := by
      simp [normalizeEdge, encode, offset, act_mul]
    let toFibre : Fin 3 × Fin period → Fibre := fun q =>
      ⟨encode q, (hfibre (encode q)).mpr
        ⟨hfamily q.1, q.2, (hencode q).symm⟩⟩
    have hinj : Function.Injective toFibre := by
      intro a b hab
      have he : encode a = encode b := congrArg Subtype.val hab
      have hs : a.1 = b.1 := hposition_inj (congrArg Prod.snd he)
      have hn : f^[a.2.val] x = f^[b.2.val] x := by
        simpa only [hencode] using congrArg (normalizeEdge u v) he
      have hi : a.2 = b.2 := Fin.ext
        ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod a.2.isLt b.2.isLt).mp hn)
      exact Prod.ext hs hi
    have hsurj : Function.Surjective toFibre := by
      intro a
      obtain ⟨ha, n, hn⟩ := (hfibre a.val).mp a.property
      refine ⟨(phase a.val.2, n), Subtype.ext ?_⟩
      change encode (phase a.val.2, n) = a.val
      apply Prod.ext
      · dsimp only [encode]
        rw [hposition _ ha, hn]
        simp [normalizeEdge, offset, act_mul]
      · exact hposition _ ha
    let e : (Fin 3 × Fin period) ≃ Fibre := Equiv.ofBijective toFibre ⟨hinj, hsurj⟩
    have htotal : Nat.card Fibre = 3 * period := by
      calc
        Nat.card Fibre = Nat.card (Fin 3 × Fin period) := (Nat.card_congr e).symm
        _ = 3 * period := by rw [Nat.card_prod, Nat.card_fin, Nat.card_fin]
    have hslot (s : Fin 3) :
        Nat.card {a : Fibre // a.val.2 = position s} = period := by
      let fixed : {q : Fin 3 × Fin period // q.1 = s} ≃ Fin period :=
        { toFun := fun q => q.val.2
          invFun := fun n => ⟨(s, n), rfl⟩
          left_inv := by
            intro q
            apply Subtype.ext
            exact Prod.ext q.property.symm rfl
          right_inv := fun _ => rfl }
      let restricted : {q : Fin 3 × Fin period // q.1 = s} ≃
          {a : Fibre // a.val.2 = position s} :=
        e.subtypeEquiv (fun q => by
          change q.1 = s ↔ position q.1 = position s
          exact hposition_inj.eq_iff.symm)
      calc
        Nat.card {a : Fibre // a.val.2 = position s} =
            Nat.card {q : Fin 3 × Fin period // q.1 = s} :=
          (Nat.card_congr restricted).symm
        _ = Nat.card (Fin period) := Nat.card_congr fixed
        _ = period := Nat.card_fin period
    have hmiddle : Nat.card {a : Fibre // a.val.2 = middle} = period := by
      cases high
      · simpa [position, middle] using hslot 2
      · simpa [position, middle] using hslot 1
    have hend : Nat.card {a : Fibre // a.val.2 ≠ middle} = 2 * period := by
      calc
        Nat.card {a : Fibre // a.val.2 ≠ middle} =
            Nat.card Fibre - Nat.card {a : Fibre // a.val.2 = middle} := by
          simpa only [Nat.card_eq_fintype_card] using
            Fintype.card_subtype_compl (fun a : Fibre => a.val.2 = middle)
        _ = 2 * period := by rw [htotal, hmiddle]; omega
    exact ⟨hpositive, htotal, hslot, hmiddle, hend, by rw [hend, hmiddle]⟩
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let whole ← Lean.Meta.getLocalDeclFromUserName `hwhole
      let some raw := whole.value? |
        Lean.throwError "AXIOMS54: hwhole must have a visible let value"
      let raw ← Lean.instantiateMVars raw
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let wholeType ← Lean.instantiateMVars whole.type
      if raw.hasMVar || target.hasMVar || wholeType.hasMVar then
        Lean.throwError "AXIOMS54: unresolved expression or universe metavariables"
      unless ← Lean.Meta.isDefEq wholeType target do
        Lean.throwError "AXIOMS54: hwhole type differs from the original conclusion"
      unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType raw) target do
        Lean.throwError "AXIOMS54: whole proof has the wrong conclusion"
      let originalNames : Array Lean.Name :=
        #[`G, `Ω, `groupInst, `actionInst, `finiteInst, `u, `v, `high, `x]
      let mut params : Array Lean.Expr := #[]
      for originalName in originalNames do
        let decl ← Lean.Meta.getLocalDeclFromUserName originalName
        if (decl.value? (allowNondep := true)).isSome then
          Lean.throwError m!"AXIOMS54: original parameter is a local let: {originalName}"
        params := params.push (Lean.mkFVar decl.fvarId)
      unless params.size == 9 do
        Lean.throwError m!"AXIOMS54: expected original 9 parameters, got {params.size}"
      let proof ← Lean.instantiateMVars (← Lean.Meta.mkLambdaFVars params raw)
      let proofType ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
      let expectedType ← Lean.instantiateMVars (← Lean.Meta.mkForallFVars params target)
      if proof.hasMVar || proofType.hasMVar || expectedType.hasMVar then
        Lean.throwError "AXIOMS54: closed proof or type still has metavariables"
      if proof.hasFVar || proofType.hasFVar || expectedType.hasFVar then
        Lean.throwError "AXIOMS54: proof has assumptions beyond the original parameters"
      if proof.hasLooseBVars || proofType.hasLooseBVars || expectedType.hasLooseBVars then
        Lean.throwError "AXIOMS54: closed proof or type has loose bound variables"
      unless ← Lean.Meta.isDefEq proofType expectedType do
        Lean.throwError "AXIOMS54: closed proof does not have the original full telescope"
      let mut constants : Lean.NameSet := {}
      for constant in proof.getUsedConstants do
        constants := constants.insert constant
      for constant in proofType.getUsedConstants do
        constants := constants.insert constant
      let env := (← Lean.getEnv).setExporting false
      let mut axioms : Lean.NameSet := {}
      for constant in constants.toArray.qsort Lean.Name.lt do
        if (env.checked.get.find? constant).isNone then
          Lean.throwError m!"AXIOMS54: constant absent from checked environment: {constant}"
        for axiomName in ← Lean.collectAxioms constant do
          axioms := axioms.insert axiomName
      let axiomNames := axioms.toArray.qsort Lean.Name.lt
      let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
      for axiomName in axiomNames do
        unless allowed.contains axiomName do
          Lean.throwError m!"AXIOMS54: disallowed axiom dependency: {axiomName}"
      let names := String.intercalate ", " (axiomNames.toList.map toString)
      Lean.logInfo m!"CFMP_ACTUAL_EDGE_FIBRE435_AXIOMS54 exact_axioms=[{names}] constant_count={constants.toArray.size} original_parameter_count={params.size}"
  exact hwhole
