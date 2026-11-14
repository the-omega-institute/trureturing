/-
Source-only implementation.  Native elaboration and kernel acceptance are pending.
The declarations below add the original weak-module bidual evaluation bridge;
all supplied duality, realization, classification, and ModuleHom records remain
literal inputs.  The arbitrary-multiplicity map is the algebraic evaluation map;
only the inverse ModuleIso uses finite multiplicities.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleDuality
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleBiduality

open LatticeGeneratingFieldLocality LatticeDiscriminantTheta
open LatticeDualCosetModule LatticeDualCosetTransport LatticeChargedTransport
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleHom ActualWeakModuleRealization ActualWeakModuleDuality
open FullJacobiCurrentTransport FullJacobiIntertwiner

universe u v w
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section Canonical
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X)
variable (hD : (gramReal D).PosDef)

/-- The actual realization projection, transported in its dependent codomain.
This map is consumed by the equivalence readback below. -/
def dualKappa (c : Discriminant D) :
    Multiplicity (dualModule A) (-c) →ₗ[ℂ] Module.Dual ℂ (Multiplicity A c) := by
  exact (LinearEquiv.cast (R := ℂ)
    (M := fun d => Module.Dual ℂ (Multiplicity A d)) (neg_neg c)).toLinearMap.comp
      (kappa (DualMultiplicity A) (-c))

/-- The supplied realization equivalence, with the literal neg_neg index read back. -/
def dualMultiplicityEquiv (c : Discriminant D) :
    Multiplicity (dualModule A) (-c) ≃ₗ[ℂ] Module.Dual ℂ (Multiplicity A c) := by
  exact (multiplicityEquiv (DualMultiplicity A) hD (-c)).trans
    (LinearEquiv.cast (R := ℂ)
      (M := fun d => Module.Dual ℂ (Multiplicity A d)) (neg_neg c))

@[simp] theorem dualMultiplicityEquiv_apply (c : Discriminant D)
    (z : Multiplicity (dualModule A) (-c)) :
    dualMultiplicityEquiv A hD c z = dualKappa A c z := by
  rfl

@[simp] theorem dualMultiplicityEquiv_symm_apply (c : Discriminant D)
    (φ : Module.Dual ℂ (Multiplicity A c)) :
    (dualMultiplicityEquiv A hD c).symm φ = dualIota A c φ := by
  rfl

/-- The actual multiplicity component of algebraic bidual evaluation. -/
def bidualFamily : Families A (dualModule (dualModule A)) := fun c =>
  (iota (DualMultiplicity (dualModule A)) c).comp
    ((dualMultiplicityEquiv A hD c).dualMap.toLinearMap.comp
      (Module.Dual.eval ℂ (Multiplicity A c)))

/-- The canonical original ModuleHom A -> dualModule (dualModule A). -/
def bidualHom : ModuleHom A (dualModule (dualModule A)) :=
  extend hD (bidualFamily A hD)

include hD in
/-- The finite-dimensional reflexivity instance is obtained on the original
multiplicity; no finiteness of the oscillator or whole carrier is used. -/
private theorem dualMultiplicity_finite
    [∀ c : Discriminant D, Module.Finite ℂ (Multiplicity A c)]
    (c : Discriminant D) : Module.Finite ℂ (Multiplicity (dualModule A) c) := by
  let e := multiplicityEquiv (DualMultiplicity A) hD c
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- The ordinary evaluation naturality supplier, retained on the actual
multiplicity maps used below. -/
theorem eval_natural (c : Discriminant D)
    {Y : Type v} [AddCommGroup Y] [Module ℂ Y]
    (f : Multiplicity A c →ₗ[ℂ] Y) :
    f.dualMap.dualMap.comp (Module.Dual.eval ℂ (Multiplicity A c)) =
      (Module.Dual.eval ℂ Y).comp f := by
  exact Module.Dual.eval_naturality f

/-- Cancel the actual outer realization and transpose before choosing a finite inverse. -/
private theorem linear_inverse_left (c : Discriminant D)
    (r : Module.Dual ℂ (Module.Dual ℂ (Multiplicity A c)) →ₗ[ℂ] Multiplicity A c)
    (hr : ∀ x, r (Module.Dual.eval ℂ (Multiplicity A c) x) = x)
    (x : Multiplicity A c) :
    r ((dualMultiplicityEquiv A hD c).dualMap.symm
      (kappa (DualMultiplicity (dualModule A)) c (bidualFamily A hD c x))) = x := by
  have hk : kappa (DualMultiplicity (dualModule A)) c (bidualFamily A hD c x) =
      ((dualMultiplicityEquiv A hD c).dualMap.toLinearMap.comp
        (Module.Dual.eval ℂ (Multiplicity A c))) x := by
    unfold bidualFamily
    -- Build the supplied cancellation with its saved instance arguments and
    -- transport the closed instance proofs by equality, rather than conversion.
    run_tac Lean.Elab.Tactic.withMainContext do
      let target ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
      let normalize (e : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr × Array (Lean.Expr × Lean.Expr)) := do
        let e ← Lean.instantiateMVars e
        let mut todo := #[e]
        let mut seen : Lean.ExprSet := {}
        let mut params : Array Lean.Expr := #[]
        let mut i := 0
        while i < todo.size do
          let p := todo[i]!
          i := i+1
          if !seen.contains p then
            seen := seen.insert p
            let n := p.getAppFn.constName?.getD .anonymous
            if !p.hasLooseBVars && !p.hasFVar &&
                (n == `Algebra.to_smulCommClass || n == `IsScalarTower.to_smulCommClass ||
                 n == `instSMulCommClassOfIsScalarTower || n == `RingHomInvPair.ids ||
                 n == `RingHomCompTriple.ids || (n.toString.splitOn "._proof_").length > 1) then
              if ← Lean.Meta.isProof p then
                params := params.push p
            match p with
            | .app f x => todo := (todo.push f).push x
            | .lam _ t b _ | .forallE _ t b _ => todo := (todo.push t).push b
            | .letE _ t v b _ => todo := ((todo.push t).push v).push b
            | .mdata _ b | .proj _ _ b => todo := todo.push b
            | _ => pure ()
        let mut replacements : Array (Lean.Expr × Lean.Expr) := #[]
        let mut current := e
        let mut transport ← Lean.Meta.mkEqRefl e
        for p in params do
          let tp ← Lean.Meta.inferType p
          if !(tp.isAppOf `SMulCommClass || tp.isAppOf `RingHomCompTriple ||
              tp.isAppOf `RingHomInvPair) then
            continue
          let q ← Lean.Meta.synthInstance tp
          let q ← Lean.instantiateMVars q
          if p != q then
            let h ← Lean.Meta.mkAppM `Subsingleton.elim #[p,q]
            let step ← Lean.Meta.withLocalDeclD `comm tp fun v => do
              let body := current.replace fun x => if x == p then some v else none
              let motive ← Lean.Meta.mkLambdaFVars #[v] body
              Lean.Meta.mkCongrArg motive h
            transport ← Lean.Meta.mkEqTrans transport step
            replacements := replacements.push (p,q)
            current := current.replace fun x => if x == p then some q else none
        return (current,transport,replacements)
      let (_,ht,replacements) ← normalize target
      let canon (e : Lean.Expr) := replacements.foldl (fun acc (p,q) =>
        acc.replace fun x => if x == p then some q else none) e
      let some (_,lhs,_) := target.eq? | throwError "expected a cancellation equality"
      let za := lhs.getAppArgs.back!.getAppArgs
      let ca := za[za.size-2]!.getAppArgs
      let i := canon ca[ca.size-2]!
      let g := canon ca.back!
      let y ← Lean.Meta.mkAppM `DFunLike.coe #[g,za.back!]
      let proof ← Lean.Meta.mkAppOptM
        `D5.S3.VertexAlgebra.Modules.ActualWeakModuleRealization.kappa_iota
        (i.getAppArgs.map some ++ #[some y])
      let finalProof ← Lean.Meta.mkEqMPR ht proof
      Lean.Elab.Tactic.closeMainGoal `literal_cancel finalProof
  have he : ((dualMultiplicityEquiv A hD c).dualMap.toLinearMap.comp
      (Module.Dual.eval ℂ (Multiplicity A c))) x =
      (dualMultiplicityEquiv A hD c).dualMap
        (Module.Dual.eval ℂ (Multiplicity A c) x) := LinearMap.comp_apply _ _ x
  exact (congrArg (fun z => r ((dualMultiplicityEquiv A hD c).dualMap.symm z)) hk).trans
    ((congrArg (fun z => r ((dualMultiplicityEquiv A hD c).dualMap.symm z)) he).trans
      ((congrArg (fun z => r z)
        ((dualMultiplicityEquiv A hD c).dualMap.symm_apply_apply
          (Module.Dual.eval ℂ (Multiplicity A c) x))).trans (hr x)))


end Canonical

section Natural
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
variable (hD : (gramReal D).PosDef)

private def dualDualFamily (f : ModuleHom A B) :
    Families (dualModule (dualModule A)) (dualModule (dualModule B)) := fun c =>
  (iota (DualMultiplicity (dualModule B)) c).comp
    (((restrict (dualHom hD f) (-c)).dualMap).comp
      (kappa (DualMultiplicity (dualModule A)) c))

/-- Transport contravariant naturality through ordinary equivalences before
substituting the concrete realized multiplicity types. -/
private theorem dualMultiplicityEquiv_natural
    {M : Type*} {N : Type*} {P : Type*} {Q : Type*} (eM : P ≃ M) (eN : Q ≃ N)
    (iM : M → P) (iN : N → Q)
    (hM : ∀ φ, eM.symm φ = iM φ) (hN : ∀ ψ, eN.symm ψ = iN ψ)
    (g : Q → P) (t : N → M)
    (h : ∀ ψ, g (iN ψ) = iM (t ψ)) (q : Q) :
    eM (g q) = t (eN q) := by
  have hq : iN (eN q) = q := (hN (eN q)).symm.trans (eN.symm_apply_apply q)
  have hg := (congrArg g hq.symm).trans (h (eN q))
  exact (congrArg eM (hg.trans (hM (t (eN q))).symm)).trans
    (eM.apply_symm_apply (t (eN q)))

private theorem dualDualFamily_natural (f : ModuleHom A B)
    (c : Discriminant D) (x : Multiplicity A c) :
    dualDualFamily hD f c (bidualFamily A hD c x) =
      bidualFamily B hD c (restrict f c x) := by
  have transpose
      {M P : Type u} {N Q : Type v}
      [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N]
      [AddCommMonoid P] [Module ℂ P] [AddCommMonoid Q] [Module ℂ Q]
      (eA : P ≃ₗ[ℂ] Module.Dual ℂ M) (eB : Q ≃ₗ[ℂ] Module.Dual ℂ N)
      (iA : Module.Dual ℂ M → P) (iB : Module.Dual ℂ N → Q)
      (hA : ∀ φ, eA.symm φ = iA φ) (hB : ∀ φ, eB.symm φ = iB φ)
      (g : Q →ₗ[ℂ] P) (f : M →ₗ[ℂ] N)
      (h : ∀ φ, g (iB φ) = iA (φ.comp f)) (x : M) :
      g.dualMap (eA.dualMap (Module.Dual.eval ℂ M x)) =
        eB.dualMap (Module.Dual.eval ℂ N (f x)) := by
    as_aux_lemma =>
      apply LinearMap.ext
      intro q
      exact LinearMap.congr_fun
        (dualMultiplicityEquiv_natural eA.toEquiv eB.toEquiv iA iB hA hB g
          (fun φ => φ.comp f) h q) x
  have hn := transpose (dualMultiplicityEquiv A hD c) (dualMultiplicityEquiv B hD c)
    (dualIota A c) (dualIota B c)
    (dualMultiplicityEquiv_symm_apply A hD c)
    (dualMultiplicityEquiv_symm_apply B hD c)
    (restrict (dualHom hD f) (-c)) (restrict f c)
    (dualHom_dualIota hD f c) x
  unfold dualDualFamily bidualFamily
  -- Match the saved realization inclusions and transposes pointwise.
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
    let normalize (e : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr × Array (Lean.Expr × Lean.Expr)) := do
      let e ← Lean.instantiateMVars e
      let mut todo := #[e]
      let mut seen : Lean.ExprSet := {}
      let mut params : Array Lean.Expr := #[]
      let mut i := 0
      while i < todo.size do
        let p := todo[i]!
        i := i+1
        if !seen.contains p then
          seen := seen.insert p
          let n := p.getAppFn.constName?.getD .anonymous
          if !p.hasLooseBVars && !p.hasFVar &&
              (n == `Algebra.to_smulCommClass || n == `IsScalarTower.to_smulCommClass ||
               n == `instSMulCommClassOfIsScalarTower || n == `RingHomInvPair.ids ||
               n == `RingHomCompTriple.ids || (n.toString.splitOn "._proof_").length > 1) then
            if ← Lean.Meta.isProof p then
              params := params.push p
          match p with
          | .app f x => todo := (todo.push f).push x
          | .lam _ t b _ | .forallE _ t b _ => todo := (todo.push t).push b
          | .letE _ t v b _ => todo := ((todo.push t).push v).push b
          | .mdata _ b | .proj _ _ b => todo := todo.push b
          | _ => pure ()
      let mut replacements : Array (Lean.Expr × Lean.Expr) := #[]
      let mut current := e
      let mut transport ← Lean.Meta.mkEqRefl e
      for p in params do
        let tp ← Lean.Meta.inferType p
        if !(tp.isAppOf `SMulCommClass || tp.isAppOf `RingHomCompTriple ||
              tp.isAppOf `RingHomInvPair) then
          continue
        let q ← Lean.Meta.synthInstance tp
        let q ← Lean.instantiateMVars q
        if p != q then
          let h ← Lean.Meta.mkAppM `Subsingleton.elim #[p,q]
          let step ← Lean.Meta.withLocalDeclD `comm tp fun v => do
            let body := current.replace fun x => if x == p then some v else none
            let motive ← Lean.Meta.mkLambdaFVars #[v] body
            Lean.Meta.mkCongrArg motive h
          transport ← Lean.Meta.mkEqTrans transport step
          replacements := replacements.push (p,q)
          current := current.replace fun x => if x == p then some q else none
      return (current,transport,replacements)
    let (_,ht,replacements) ← normalize target
    let canon (e : Lean.Expr) := replacements.foldl (fun acc (p,q) =>
      acc.replace fun x => if x == p then some q else none) e
    let expose (e : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
      let mut value := canon e.consumeMData
      for _ in [:8] do
        value := value.consumeMData
        let args := value.getAppArgs
        unless value.isAppOf `DFunLike.coe && args.size >= 2 do
          throwError "expected a linear-map application, got {value.getAppFn.constName?}"
        let map := (canon args[args.size-2]!).consumeMData
        let z := canon args.back!
        if map.isAppOf `LinearMap.comp then
          let maps := map.getAppArgs
          unless maps.size >= 2 do throwError "incomplete composition"
          let inner ← Lean.Meta.mkAppM `DFunLike.coe #[maps.back!,z]
          value ← Lean.Meta.mkAppM `DFunLike.coe #[maps[maps.size-2]!,inner]
        else
          return (map,z)
      throwError "unexpected composition depth in saved bidual family"
    let some (_,lhs,_) := target.eq? | throwError "expected a naturality equality"
    let (iB,bValue) ← expose lhs
    let (t,kValue) ← expose bValue
    let (_,aValue) ← expose kValue
    let (iA,y) ← expose aValue
    unless iA.isAppOf `D5.S3.VertexAlgebra.Modules.ActualWeakModuleRealization.iota &&
        iB.isAppOf `D5.S3.VertexAlgebra.Modules.ActualWeakModuleRealization.iota do
      throwError "expected the two saved realization inclusions"
    let hki ← Lean.Meta.mkAppOptM
      `D5.S3.VertexAlgebra.Modules.ActualWeakModuleRealization.kappa_iota
      (iA.getAppArgs.map some ++ #[some y])
    let tFun ← Lean.Meta.mkAppM `DFunLike.coe #[t]
    let first ← Lean.Meta.mkCongrArg tFun hki
    let lctx ← Lean.getLCtx
    let some hnDecl := lctx.findFromUserName? `hn | throwError "missing pointwise naturality"
    let naturalProof := Lean.Expr.fvar hnDecl.fvarId
    let naturalType ← Lean.instantiateMVars (← Lean.Meta.inferType naturalProof)
    let (_,naturalTransport,_) ← normalize naturalType
    let normalizedNaturalProof ← Lean.Meta.mkEqMP naturalTransport naturalProof
    let middle ← Lean.Meta.mkEqTrans first normalizedNaturalProof
    let iFun ← Lean.Meta.mkAppM `DFunLike.coe #[iB]
    let proof ← Lean.Meta.mkCongrArg iFun middle
    let actual ← Lean.Meta.whnf (← Lean.Meta.inferType proof)
    let (_,ha,_) ← normalize actual
    let normalizedProof ← Lean.Meta.mkEqMP ha proof
    let finalProof ← Lean.Meta.mkEqMPR ht normalizedProof
    Lean.Elab.Tactic.closeMainGoal `literal_natural finalProof


theorem bidualHom_natural (f : ModuleHom A B) :
    (bidualHom B hD).comp f =
      (dualHom hD (dualHom hD f)).comp (bidualHom A hD) := by
  apply (recordEquiv A (dualModule (dualModule B))).injective
  apply (homMultiplicityEquiv A (dualModule (dualModule B)) hD).injective
  funext c
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change ((bidualHom B hD).comp f).linearMap (x.val : X) =
    ((dualHom hD (dualHom hD f)).comp (bidualHom A hD)).linearMap (x.val : X)
  have hl := extend_ground hD (bidualFamily B hD) c (restrict f c x)
  have hr := extend_ground hD (dualDualFamily hD f) c (bidualFamily A hD c x)
  have ha := extend_ground hD (bidualFamily A hD) c x
  change (extend hD (bidualFamily B hD)).linearMap (restrict f c x).val.val =
    (extend hD (dualDualFamily hD f)).linearMap
      ((extend hD (bidualFamily A hD)).linearMap x.val.val)
  exact hl.trans
    ((congrArg (fun t : Multiplicity (dualModule (dualModule B)) c => t.val.val)
      (dualDualFamily_natural hD f c x).symm).trans
        (((congrArg (extend hD (dualDualFamily hD f)).linearMap.toAddHom.toFun ha).trans hr).symm))

end Natural

section FiniteIso
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X)
variable (hD : (gramReal D).PosDef)
variable [∀ c : Discriminant D, Module.Finite ℂ (Multiplicity A c)]

/-- The inverse family uses the actual kappa of the outer realization and the
finite-dimensional `Module.evalEquiv` on the original multiplicity. -/
def bidualInverseFamily :
    Families (dualModule (dualModule A)) A := fun c =>
  (Module.evalEquiv ℂ (Multiplicity A c)).symm.toLinearMap.comp
    ((dualMultiplicityEquiv A hD c).dualMap.symm.toLinearMap.comp
      (kappa (DualMultiplicity (dualModule A)) c))

private theorem bidualInverseFamily_left (c : Discriminant D)
    (x : Multiplicity A c) :
    bidualInverseFamily A hD c (bidualFamily A hD c x) = x := by
  set_option synthInstance.maxHeartbeats 200000 in
    have he (y : Multiplicity A c) :
      (Module.evalEquiv ℂ (Multiplicity A c)).symm
        (Module.Dual.eval ℂ (Multiplicity A c) y) = y := by
      simpa only [Module.evalEquiv_apply] using
        (Module.evalEquiv ℂ (Multiplicity A c)).symm_apply_apply y
    exact linear_inverse_left A hD c
      (Module.evalEquiv ℂ (Multiplicity A c)).symm.toLinearMap he x

private theorem bidualInverseFamily_right (c : Discriminant D)
    (z : Multiplicity (dualModule (dualModule A)) c) :
    bidualFamily A hD c (bidualInverseFamily A hD c z) = z := by
  have comp_inj {M N P : Type u}
      [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N]
      [AddCommMonoid P] [Module ℂ P]
      (f : N →ₗ[ℂ] P) (g : M →ₗ[ℂ] N)
      (hf : Function.Injective f) (hg : Function.Injective g) :
      Function.Injective (f.comp g) := by
    as_aux_lemma => exact hf.comp hg
  have hi : Function.Injective (bidualInverseFamily A hD c) := by
    unfold bidualInverseFamily
    -- Transport the closed scalar-instance proofs explicitly. This keeps the
    -- realization and dual maps literal while avoiding deep proof-irrelevance conversion.
    run_tac Lean.Elab.Tactic.withMainContext do
      let target ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
      let normalize (e : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
        let e ← Lean.instantiateMVars e
        let mut todo := #[e]
        let mut seen : Lean.ExprSet := {}
        let mut params : Array Lean.Expr := #[]
        let mut i := 0
        while i < todo.size do
          let p := todo[i]!
          i := i+1
          if !seen.contains p then
            seen := seen.insert p
            let n := p.getAppFn.constName?.getD .anonymous
            if !p.hasLooseBVars && !p.hasFVar &&
                (n == `Algebra.to_smulCommClass || n == `IsScalarTower.to_smulCommClass ||
                 n == `instSMulCommClassOfIsScalarTower || n == `RingHomInvPair.ids ||
                 n == `RingHomCompTriple.ids || (n.toString.splitOn "._proof_").length > 1) then
              if ← Lean.Meta.isProof p then
                params := params.push p
            match p with
            | .app f x => todo := (todo.push f).push x
            | .lam _ t b _ | .forallE _ t b _ => todo := (todo.push t).push b
            | .letE _ t v b _ => todo := ((todo.push t).push v).push b
            | .mdata _ b | .proj _ _ b => todo := todo.push b
            | _ => pure ()
        let mut current := e
        let mut transport ← Lean.Meta.mkEqRefl e
        for p in params do
          let tp ← Lean.Meta.inferType p
          if !(tp.isAppOf `SMulCommClass || tp.isAppOf `RingHomCompTriple ||
              tp.isAppOf `RingHomInvPair) then
            continue
          let q ← Lean.Meta.synthInstance tp
          let q ← Lean.instantiateMVars q
          if p != q then
            let h ← Lean.Meta.mkAppM `Subsingleton.elim #[p,q]
            let step ← Lean.Meta.withLocalDeclD `comm tp fun v => do
              let body := current.replace fun x => if x == p then some v else none
              let motive ← Lean.Meta.mkLambdaFVars #[v] body
              Lean.Meta.mkCongrArg motive h
            transport ← Lean.Meta.mkEqTrans transport step
            current := current.replace fun x => if x == p then some q else none
        return (current,transport)
      let (normal,ht) ← normalize target
      let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar normal
      let castProof ← Lean.Meta.mkEqMPR ht next
      (← Lean.Elab.Tactic.getMainGoal).assign castProof
      Lean.Elab.Tactic.replaceMainGoal [next.mvarId!]
    apply comp_inj
    · exact (Module.evalEquiv ℂ (Multiplicity A c)).symm.injective
    · apply comp_inj
      · exact (dualMultiplicityEquiv A hD c).dualMap.symm.injective
      · exact (multiplicityEquiv (DualMultiplicity (dualModule A)) hD c).injective
  exact hi (bidualInverseFamily_left A hD c (bidualInverseFamily A hD c z))


def bidualInverseHom : ModuleHom (dualModule (dualModule A)) A :=
  extend hD (bidualInverseFamily A hD)

include hD in
private theorem hom_ext_restrict
    {M : Type v} {N : Type w} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N]
    {J : FullJacobiLatticeModule D M} {K : FullJacobiLatticeModule D N}
    (f g : ModuleHom J K) (h : restrict f = restrict g) : f = g := by
  apply (recordEquiv J K).injective
  apply (homMultiplicityEquiv J K hD).injective
  exact h

private theorem bidual_left_inverse :
    (bidualInverseHom A hD).comp (bidualHom A hD) = ModuleHom.id A := by
  apply hom_ext_restrict hD
  funext c
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change ((bidualInverseHom A hD).comp (bidualHom A hD)).linearMap (x.val : X) = x.val
  have h1 := extend_ground hD (bidualFamily A hD) c x
  have h2 := extend_ground hD (bidualInverseFamily A hD) c (bidualFamily A hD c x)
  change (extend hD (bidualInverseFamily A hD)).linearMap
    ((extend hD (bidualFamily A hD)).linearMap x.val.val) = x.val.val
  exact ((congrArg (extend hD (bidualInverseFamily A hD)).linearMap.toAddHom.toFun h1).trans h2).trans
    (congrArg (fun t : Multiplicity A c => t.val.val) (bidualInverseFamily_left A hD c x))

private theorem bidual_right_inverse :
    (bidualHom A hD).comp (bidualInverseHom A hD) =
      ModuleHom.id (dualModule (dualModule A)) := by
  apply hom_ext_restrict hD
  funext c
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  apply Subtype.ext
  change ((bidualHom A hD).comp (bidualInverseHom A hD)).linearMap (z.val : _) = z.val
  have h1 := extend_ground hD (bidualInverseFamily A hD) c z
  have h2 := extend_ground hD (bidualFamily A hD) c (bidualInverseFamily A hD c z)
  change (extend hD (bidualFamily A hD)).linearMap
    ((extend hD (bidualInverseFamily A hD)).linearMap z.val.val) = z.val.val
  exact ((congrArg (extend hD (bidualFamily A hD)).linearMap.toAddHom.toFun h1).trans h2).trans
    (congrArg (fun t : Multiplicity (dualModule (dualModule A)) c => t.val.val)
      (bidualInverseFamily_right A hD c z))

/-- Finite-multiplicity biduality as an actual original ModuleIso record. -/
def bidualIso : ModuleIso A (dualModule (dualModule A)) := by
  letI : ∀ c : Discriminant D, Module.Finite ℂ (Multiplicity (dualModule A) c) :=
    fun c => dualMultiplicity_finite A hD c
  exact {
    linearEquiv :=
      { toLinearMap := (bidualHom A hD).linearMap
        invFun := (bidualInverseHom A hD).linearMap
        left_inv := by
          intro x
          exact congrArg (fun g : ModuleHom A A => g.linearMap x)
            (bidual_left_inverse A hD)
        right_inv := by
          intro z
          exact congrArg (fun g : ModuleHom (dualModule (dualModule A))
              (dualModule (dualModule A)) => g.linearMap z)
            (bidual_right_inverse A hD) }
    intertwines := (bidualHom A hD).intertwines }

end FiniteIso
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleBiduality
