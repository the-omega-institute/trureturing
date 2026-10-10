/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphGlobal
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphGlobal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularGraphTwoLayer
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Lean Elab Term in
elab "unitGlobal%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitriangularLayersGlobal"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularLayersGlobal"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique actual filtration kernel {id} not found"
open Lean Elab Term in
elab "unitGraphTwo%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitriangularGraphTwoLayer"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularGraphTwoLayer"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique actual filtration kernel {id} not found"
namespace NikolovSegal.PartIIUnitriangularGraphGlobal
open PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitriangularGraphLayers
universe u
variable {F : Type u} [Field F] {n : ℕ}
private abbrev actualU : Subgroup (Matrix.SpecialLinearGroup (Fin n) F) := (unitGlobal% U)
private theorem corrected_graph_power_depth (u0 : Matrix.SpecialLinearGroup (Fin n) F)
    (hu0 : LayerDepth 1 (u0.val-1)) (lambda : Fˣ) (phi : RingAut F) (eps : Bool)
    (d k : ℕ) (hk : 0<k) (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) :
    LayerDepth k ((((MulAut.conj u0*(heightTorus lambda*fieldGraphAut phi eps) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) a).val-1) := by
  induction d with
  | zero => simpa only [pow_zero,MulAut.one_apply] using ha
  | succ d ih =>
    rw [pow_succ',MulAut.mul_apply,MulAut.mul_apply,MulAut.mul_apply]
    exact (unitGlobal% inner_depth) u0 hu0 k hk _ ((unitAction% torus_depth) lambda k _ ((unitGraph% field_graph_depth) phi eps k hk _ ih))

/-- Full Lemma9.2 U3 PRODUCT for arbitrary prescribed field/positive-graph
and positive q-divisor tuples, in every rank. The same fixed pre-target
corrections supply all nonlinear targets. The proved genuine graph two-layer
solver feeds the accepted exact ordered quotient accumulation. All field
scalar arithmetic is proved; no graph-layer or U3 coverage input is assumed.
First-two-layer graph supply and full-group assembly remain distinct steps. -/
theorem actual_uniform_field_graph_U3_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0<q) (hM : (2*q)*(2*q+1)<M) (hF : (2*q+1)^(2*q) < Fintype.card F)
    (phiP phiN : Fin M → RingAut F) (epsP epsN : Fin M → Bool) (dP dN : Fin M → ℕ)
    (hdP : ∀ i, 0<dP i ∧ dP i ∣ q) (hdN : ∀ i, 0<dN i ∧ dN i ∣ q)
    (phi0 : RingAut F) (eps0 : Bool) (d0 : ℕ) (hd0 : 0<d0 ∧ d0 ∣ q) :
    ∃ lambdaP lambdaN : Fin M → Fˣ, ∃ lambda0 : Fˣ, ∃ u0 : Matrix.SpecialLinearGroup (Fin n) F,
      LayerDepth 1 (u0.val-1) ∧ ∀ b : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth 3 (b.val-1) →
        ∃ x z : Fin M → Matrix.SpecialLinearGroup (Fin n) F, ∃ y : Matrix.SpecialLinearGroup (Fin n) F,
          (∀ i, LayerDepth 3 ((x i).val-1) ∧ LayerDepth 3 ((z i).val-1)) ∧ LayerDepth 3 (y.val-1) ∧
          NikolovSegal.orderedProduct (fun i =>
            (x i)⁻¹*((mirrorTorus (lambdaP i)*fieldGraphAut (phiP i) (epsP i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dP i)) (x i))*
          NikolovSegal.orderedProduct (fun i =>
            (z i)⁻¹*((mirrorTorus ((lambdaN i)⁻¹)*fieldGraphAut (phiN i) (epsN i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dN i)) (z i))*
          (y⁻¹*((MulAut.conj u0*(heightTorus lambda0*fieldGraphAut phi0 eps0) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d0) y)=b := by
  classical
  obtain ⟨lambdaP,lambdaN,lambda0,u0,hu0,hlocal⟩ :=
    PartIIUnitriangularGraphTwoLayer.actual_uniform_field_graph_two_layer_lift (n:=n) hq hM hF phiP phiN epsP epsN dP dN hdP hdN phi0 eps0 d0 hd0
  let deltaP : Fin M → MulAut (Matrix.SpecialLinearGroup (Fin n) F) := fun i => (mirrorTorus (lambdaP i)*fieldGraphAut (phiP i) (epsP i))^(dP i)
  let deltaN : Fin M → MulAut (Matrix.SpecialLinearGroup (Fin n) F) := fun i => (mirrorTorus ((lambdaN i)⁻¹)*fieldGraphAut (phiN i) (epsN i))^(dN i)
  let delta0 : MulAut (Matrix.SpecialLinearGroup (Fin n) F) := (MulAut.conj u0*(heightTorus lambda0*fieldGraphAut phi0 eps0))^d0
  have hp : ∀ k, 0<k → ∀ i a, LayerDepth k (a.val-1) → LayerDepth k (((deltaP i) a).val-1) := by
    intro k hk i a ha; exact (unitGraph% mirror_graph_depth) (lambdaP i) (phiP i) (epsP i) k hk a ha (dP i)
  have hn : ∀ k, 0<k → ∀ i a, LayerDepth k (a.val-1) → LayerDepth k (((deltaN i) a).val-1) := by
    intro k hk i a ha; exact (unitGraph% mirror_graph_depth) ((lambdaN i)⁻¹) (phiN i) (epsN i) k hk a ha (dN i)
  have h0 : ∀ k, 0<k → ∀ a, LayerDepth k (a.val-1) → LayerDepth k ((delta0 a).val-1) := by
    intro k hk a ha; exact corrected_graph_power_depth u0 hu0 lambda0 phi0 eps0 d0 k hk a ha
  let alphaP := fun i => (unitGlobal% restriction) (deltaP i) (hp 1 (by decide) i)
  let alphaN := fun i => (unitGlobal% restriction) (deltaN i) (hn 1 (by decide) i)
  let alpha0 := (unitGlobal% restriction) delta0 (h0 1 (by decide))
  have hpU : ∀ k, 0<k → ∀ i a, LayerDepth k (a.val.val-1) → LayerDepth k (((alphaP i) a).val.val-1) := by
    intro k hk i a ha
    rw [(unitGlobal% restriction_apply)]
    exact hp k hk i a.val ha
  have hnU : ∀ k, 0<k → ∀ i a, LayerDepth k (a.val.val-1) → LayerDepth k (((alphaN i) a).val.val-1) := by
    intro k hk i a ha
    rw [(unitGlobal% restriction_apply)]
    exact hn k hk i a.val ha
  have h0U : ∀ k, 0<k → ∀ a, LayerDepth k (a.val.val-1) → LayerDepth k ((alpha0 a).val.val-1) := by
    intro k hk a ha
    rw [(unitGlobal% restriction_apply)]
    exact h0 k hk a.val ha
  have hlocalU : ∀ d : ℕ, ∀ b : actualU (F:=F) (n:=n), LayerDepth (2*d+3) (b.val.val-1) →
      ∃ t s : Fin M → actualU (F:=F) (n:=n), ∃ v : actualU (F:=F) (n:=n),
        (∀ i, LayerDepth (2*d+3) ((t i).val.val-1) ∧ LayerDepth (2*d+3) ((s i).val.val-1)) ∧
        LayerDepth (2*d+3) (v.val.val-1) ∧
        LayerDepth (2*d+5) ((((unitGlobal% systemValue) alphaP alphaN alpha0 t s v)⁻¹*b).val.val-1) := by
    intro d b hb
    obtain ⟨t,s,v,hts,hv,hres⟩ := hlocal (2*d+3) (by omega) (by omega) b.val hb
    let T : Fin M → actualU (F:=F) (n:=n) := fun i => ⟨t i,(unitLayer% depth_mono) (hts i).1 (by omega)⟩
    let S : Fin M → actualU (F:=F) (n:=n) := fun i => ⟨s i,(unitLayer% depth_mono) (hts i).2 (by omega)⟩
    let V : actualU (F:=F) (n:=n) := ⟨v,(unitLayer% depth_mono) hv (by omega)⟩
    refine ⟨T,S,V,hts,hv,?_⟩
    change LayerDepth (2*d+5) ((((unitGlobal% systemValue) alphaP alphaN alpha0 T S V).val⁻¹*b.val).val-1)
    rw [(unitGlobal% real_system) deltaP deltaN delta0 (hp 1 (by decide)) (hn 1 (by decide)) (h0 1 (by decide)) T S V]
    simpa only [show 2*d+3+2=2*d+5 by omega] using hres
  refine ⟨lambdaP,lambdaN,lambda0,u0,hu0,?_⟩
  intro b hb
  let B : actualU (F:=F) (n:=n) := ⟨b,(unitLayer% depth_mono) hb (by omega)⟩
  obtain ⟨x,z,y,hxz,hy,he⟩ := (unitGlobal% finite_layer_reconstruction) alphaP alphaN alpha0 hpU hnU h0U hlocalU B hb
  refine ⟨fun i => (x i).val,fun i => (z i).val,y.val,hxz,hy,?_⟩
  have h := congrArg Subtype.val he
  rw [(unitGlobal% real_system) deltaP deltaN delta0 (hp 1 (by decide)) (hn 1 (by decide)) (h0 1 (by decide)) x z y] at h
  exact h
end NikolovSegal.PartIIUnitriangularGraphGlobal
