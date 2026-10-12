/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnDisplacedClassWords
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnDisplacedClassWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIISLnUnipotentCommutators
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Products.PartIIConjugacyValueConsumption
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Logic.Equiv.Fintype

/-! Actual matrix displacement toward the small-field Section5 width
kernel. A displaced coordinate block and its image commute by literal
matrix support. This turns each of the THREE proved block commutators
into FOUR genuine conjugates of the fixed permutation matrix.
The geometric displacement condition is not a coverage assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Lean Elab Term in
elab "cycleClass%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIFixedSLnPower"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIIFixedSLnPower"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique accepted fixed-cycle kernel {id} not found"

namespace NikolovSegal.PartIISLnDisplacedClassWords
open Matrix Equiv
universe u
variable {F : Type u} [Field F] {N d : ℕ}

/-- Literal identity outside a principal coordinate block. -/
def Supported (T : Set (Fin N)) (a : SpecialLinearGroup (Fin N) F) : Prop :=
  ∀ i j, i∉T ∨ j∉T → a i j=(1:Matrix (Fin N) (Fin N) F) i j

private abbrev permSL (sigma : Perm (Fin N)) (hs : Perm.sign sigma=1) :
    SpecialLinearGroup (Fin N) F := (cycleClass% slPerm) sigma hs
private abbrev permMatrix (sigma : Perm (Fin N)) : Matrix (Fin N) (Fin N) F :=
  (cycleClass% pMatrix) sigma

private theorem support_commute {T U : Set (Fin N)} (hTU : Disjoint T U)
    {a b : SpecialLinearGroup (Fin N) F} (ha : Supported T a) (hb : Supported U b) :
    Commute a b := by
  classical
  have hz (a b : SpecialLinearGroup (Fin N) F) (T U : Set (Fin N))
      (hTU : Disjoint T U) (ha : Supported T a) (hb : Supported U b) :
      (a.val-1)*(b.val-1)=0 := by
    ext i j
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro t ht
    by_cases h : t∈T
    · have h' : t∉U := fun hh => Set.disjoint_left.mp hTU h hh
      simp only [Matrix.sub_apply,hb t j (Or.inl h'),sub_self,mul_zero]
    · simp only [Matrix.sub_apply,ha i t (Or.inr h),sub_self,zero_mul]
  have hab := hz a b T U hTU ha hb
  have hba := hz b a U T hTU.symm hb ha
  change a*b=b*a
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul]
  apply sub_eq_zero.mp
  calc a.val*b.val-b.val*a.val=(a.val-1)*(b.val-1)-(b.val-1)*(a.val-1) := by noncomm_ring
       _ = 0 := by rw [hab,hba,sub_self]

private theorem permutation_conj_entry (sigma : Perm (Fin N)) (hs : Perm.sign sigma=1)
    (a : SpecialLinearGroup (Fin N) F) (i j : Fin N) :
    (permSL (F:=F) sigma hs*a*(permSL (F:=F) sigma hs)⁻¹) i j=
      a (sigma i) (sigma j) := by
  rw [(cycleClass% slPerm_inv)]
  change ((sigma.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) F)*a.val*
    (sigma⁻¹.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) F)) i j=_
  rw [PEquiv.toMatrix_toPEquiv_mul,PEquiv.mul_toMatrix_toPEquiv]
  rfl

private theorem permutation_support (sigma : Perm (Fin N)) (hs : Perm.sign sigma=1)
    (T : Set (Fin N)) (a : SpecialLinearGroup (Fin N) F) (ha : Supported T a) :
    Supported (sigma ⁻¹' T)
      (permSL (F:=F) sigma hs*a*(permSL (F:=F) sigma hs)⁻¹) := by
  intro i j hij
  rw [permutation_conj_entry]
  have h := ha (sigma i) (sigma j) hij
  simpa only [Matrix.one_apply,sigma.injective.eq_iff] using h

private def scalarAt (i : Fin N) (t : Fˣ) : Matrix (Fin N) (Fin N) F :=
  diagonal (fun j => if j=i then (t:F) else 1)
private theorem scalarAt_det (i : Fin N) (t : Fˣ) : det (scalarAt i t)=(t:F) := by
  classical
  simp [scalarAt,det_diagonal]
private theorem scalarAt_inverse (i : Fin N) (t : Fˣ) :
    scalarAt i t*scalarAt i t⁻¹=1 := by
  classical
  rw [scalarAt,scalarAt,diagonal_mul_diagonal]
  apply diagonal_eq_one.mpr
  funext j
  split_ifs <;> simp
private theorem scalarAt_commute (sigma : Perm (Fin N)) (i : Fin N)
    (hi : sigma i=i) (t : Fˣ) :
    scalarAt i t*(permMatrix (F:=F) sigma)=
      (permMatrix (F:=F) sigma)*scalarAt i t := by
  classical
  ext r c
  simp only [scalarAt,diagonal_mul,mul_diagonal,(cycleClass% pMatrix_entry)]
  by_cases hrc : sigma r=c
  · have hir : r=i ↔ c=i := by
      rw [← hrc]; exact (sigma.injective.eq_iff).symm.trans (by rw [hi])
    simp [hrc,hir]
  · simp [hrc]

/-- An actual determinant-one reversing conjugator, over every field.
The arbitrary permutation conjugator is normalized at the fixed coordinate;
no SL conjugacy/class-width premise is supplied. -/
private theorem permutation_inverse_conjugate (sigma : Perm (Fin N))
    (hs : Perm.sign sigma=1) (i : Fin N) (hi : sigma i=i) :
    ∃ c : SpecialLinearGroup (Fin N) F,
      c⁻¹*(permSL (F:=F) sigma hs)*c=
        (permSL (F:=F) sigma hs)⁻¹ := by
  classical
  obtain ⟨tau,htau⟩ := isConj_iff.mp
    (Perm.isConj_of_cycleType_eq (Perm.cycleType_inv sigma).symm)
  let t : Fˣ := (Units.map (Int.castRingHom F).toMonoidHom) (Perm.sign tau)
  let P : Matrix (Fin N) (Fin N) F := permMatrix (F:=F) tau
  let Q : Matrix (Fin N) (Fin N) F := permMatrix (F:=F) tau⁻¹
  let D := scalarAt i t⁻¹
  let E := scalarAt i t
  have hPQ : P*Q=1 := by
    dsimp only [P,Q]
    rw [(cycleClass% pMatrix_mul),inv_mul_cancel,(cycleClass% pMatrix_one)]
  have hQP : Q*P=1 := by
    dsimp only [P,Q]
    rw [(cycleClass% pMatrix_mul),mul_inv_cancel,(cycleClass% pMatrix_one)]
  have hDE : D*E=1 := scalarAt_inverse i t⁻¹
  have hED : E*D=1 := scalarAt_inverse i t
  have hdet : det (D*P)=1 := by
    rw [det_mul,scalarAt_det,(cycleClass% pMatrix_det)]
    change ((t⁻¹:Fˣ):F)*(t:F)=1
    simp
  let c : SpecialLinearGroup (Fin N) F := ⟨D*P,hdet⟩
  have hinv : c⁻¹.val=Q*E := by
    have hh : c.val*(Q*E)=1 := by
      change (D*P)*(Q*E)=1
      rw [mul_assoc,← mul_assoc P Q E,hPQ,one_mul,hDE]
    have hcc : c⁻¹.val*c.val=1 := congrArg Subtype.val (inv_mul_cancel c)
    calc c⁻¹.val = c⁻¹.val*(c.val*(Q*E)) := by rw [hh,mul_one]
         _ = Q*E := by rw [← mul_assoc,hcc,one_mul]
  refine ⟨c,?_⟩
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul,SpecialLinearGroup.coe_mul,hinv,(cycleClass% slPerm_inv)]
  change (Q*E)*(permMatrix (F:=F) sigma)*(D*P)=permMatrix (F:=F) sigma⁻¹
  have hEC := scalarAt_commute sigma i hi t
  calc
    _ = Q*(permMatrix (F:=F) sigma)*P := by
      have hEC' : E*permMatrix (F:=F) sigma=permMatrix sigma*E := hEC
      calc
        _ = Q*(E*permMatrix sigma*D)*P := by simp only [mul_assoc]
        _ = _ := by rw [hEC',mul_assoc (permMatrix sigma) E D,hED,mul_one]
    _ = _ := by
      dsimp only [Q,P]
      rw [(cycleClass% pMatrix_mul),(cycleClass% pMatrix_mul)]
      rw [← mul_assoc,htau]

private theorem displaced_four {S : Type u} [Group S] (h a b c : S)
    (hc : c⁻¹*h*c=h⁻¹) (hab : Commute (h*a*h⁻¹) b) :
    (List.ofFn (fun i : Fin 4 =>
      ((![a,c,b,c*a*b] i)⁻¹*h*(![a,c,b,c*a*b] i)))).prod=a⁻¹*b⁻¹*a*b := by
  have hcomm : (h*a*h⁻¹)*b⁻¹*(h*a*h⁻¹)⁻¹=b⁻¹ := by
    rw [hab.inv_right.eq,mul_inv_cancel_right]
  calc
    _ = a⁻¹*((h*a*h⁻¹)*b⁻¹*(h*a*h⁻¹)⁻¹)*a*b := by
      simp only [List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,
        Matrix.cons_val_zero,Matrix.cons_val_succ,mul_one]
      have h1 := hc
      have h2 : (c*a*b)⁻¹*h*(c*a*b)=b⁻¹*a⁻¹*h⁻¹*a*b := by
        calc _ = b⁻¹*a⁻¹*(c⁻¹*h*c)*a*b := by group
             _ = _ := by rw [hc]
      rw [hc,h2]
      group
    _ = _ := by rw [hcomm]
private noncomputable def padEquiv (e : (Fin d ⊕ Fin d) ↪ Fin N) :
    ((Fin d ⊕ Fin d) ⊕ ((Set.range e)ᶜ : Set (Fin N))) ≃ Fin N := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range e))

/-- Actual principal-block embedding for the selected coordinate injection. -/
noncomputable def padAlong (e : (Fin d ⊕ Fin d) ↪ Fin N) :
    SpecialLinearGroup (Fin d ⊕ Fin d) F →* SpecialLinearGroup (Fin N) F := by
  classical
  let f : SpecialLinearGroup (Fin d ⊕ Fin d) F →*
      SpecialLinearGroup ((Fin d ⊕ Fin d) ⊕ ((Set.range e)ᶜ : Set (Fin N))) F :=
    { toFun := fun a => ⟨fromBlocks a.val 0 0 1,by simp [a.prop]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [SpecialLinearGroup.coe_mul,fromBlocks_multiply]) }
  exact (SLnUnipotentWidth.reindexSL (padEquiv e)).toMonoidHom.comp f

private theorem pad_support (e : (Fin d ⊕ Fin d) ↪ Fin N)
    (a : SpecialLinearGroup (Fin d ⊕ Fin d) F) : Supported (Set.range e) (padAlong e a) := by
  classical
  intro i j hij
  obtain ⟨i,rfl⟩ := (padEquiv e).surjective i
  obtain ⟨j,rfl⟩ := (padEquiv e).surjective j
  have hl : ∀ x, padEquiv e (Sum.inl x)=e x := by intro x; rfl
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exfalso
      rcases hij with hi | hj
      · exact hi ⟨i,hl i⟩
      · exact hj ⟨j,hl j⟩
    | inr j =>
      have hne : padEquiv e (Sum.inl i)≠padEquiv e (Sum.inr j) := by
        intro h; have := (padEquiv e).injective h; cases this
      simp [padAlong,SLnUnipotentWidth.reindexSL,Matrix.reindex_apply,hne]
  | inr i =>
    cases j with
    | inl j =>
      have hne : padEquiv e (Sum.inr i)≠padEquiv e (Sum.inl j) := by
        intro h; have := (padEquiv e).injective h; cases this
      simp [padAlong,SLnUnipotentWidth.reindexSL,Matrix.reindex_apply,hne]
    | inr j =>
      simp [padAlong,SLnUnipotentWidth.reindexSL,Matrix.reindex_apply,
        Matrix.one_apply,(padEquiv e).injective.eq_iff]

/-- Twelve ACTUAL conjugacy-class factors reconstruct every upper target
on a displaced block. Displacement is a literal permutation incidence,
and all three commutators and the reversing conjugator are constructed.
This is a local matrix-width conclusion, not full-group coverage. -/
theorem actual_displaced_upper_twelve_class_factors
    (sigma : Perm (Fin N)) (hs : Perm.sign sigma=1)
    (fixed : Fin N) (hfixed : sigma fixed=fixed)
    (e : (Fin d ⊕ Fin d) ↪ Fin N)
    (hdis : ∀ x y, sigma (e x)≠e y)
    (u : SpecialLinearGroup (Fin d) F)
    (hu : PartIIUnitriangularLayers.LayerDepth 1 (u.val-1)) :
    ∃ a : Fin 12 → SpecialLinearGroup (Fin N) F,
      orderedProduct (fun i => (a i)⁻¹*(permSL (F:=F) sigma hs)*a i)=
        padAlong e (PartIISLnUnipotentCommutators.doubleEmbed u) := by
  classical
  let h := permSL (F:=F) sigma hs
  obtain ⟨c,hc⟩ := permutation_inverse_conjugate (F:=F) sigma hs fixed hfixed
  obtain ⟨a,b,hab⟩ := PartIISLnUnipotentCommutators.actual_upper_double_three_commutators u hu
  let A := fun i : Fin 3 => padAlong e (a i)
  let B := fun i : Fin 3 => padAlong e (b i)
  have hTU : Disjoint (sigma ⁻¹' Set.range e) (Set.range e) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,rfl⟩ := hy
    obtain ⟨j,hj⟩ := hx
    exact hdis i j hj.symm
  have hcomm : ∀ i, Commute (h*A i*h⁻¹) (B i) := by
    intro i
    exact support_commute hTU (permutation_support sigma hs _ _ (pad_support e _)) (pad_support e _)
  let w : Fin 3 → Fin 4 → SpecialLinearGroup (Fin N) F :=
    fun i => ![A i,c,B i,c*A i*B i]
  let W : Fin 12 → SpecialLinearGroup (Fin N) F :=
    fun k => w ((finProdFinEquiv : Fin 3 × Fin 4 ≃ Fin 12).symm k).1 ((finProdFinEquiv : Fin 3 × Fin 4 ≃ Fin 12).symm k).2
  refine ⟨W,?_⟩
  have hblocks : ∀ i, orderedProduct (fun j => (w i j)⁻¹*h*w i j)=
      (A i)⁻¹*(B i)⁻¹*A i*B i := by
    intro i
    exact displaced_four h (A i) (B i) c hc (hcomm i)
  have hprod : orderedProduct (fun k => (W k)⁻¹*h*W k)=
      orderedProduct (fun i => orderedProduct (fun j => (w i j)⁻¹*h*w i j)) := by
    simp only [orderedProduct]
    rw [List.ofFn_mul (m:=3) (n:=4)]
    simp only [List.prod_flatten,List.map_ofFn]
    refine congrArg (fun f : Fin 3 → SpecialLinearGroup (Fin N) F => (List.ofFn f).prod)
      (funext fun i => ?_)
    refine congrArg (fun f : Fin 4 → SpecialLinearGroup (Fin N) F => (List.ofFn f).prod)
      (funext fun j => ?_)
    have hk : (⟨i.val*4+j.val,by have hi := i.isLt; have hj := j.isLt; omega⟩ : Fin 12)=
        finProdFinEquiv (i,j) := by
      apply Fin.ext
      change i.val*4+j.val=j.val+4*i.val
      omega
    rw [hk]
    simp only [W,Equiv.symm_apply_apply]
  change orderedProduct (fun k => (W k)⁻¹*h*W k)=_
  rw [hprod]
  simp_rw [hblocks]
  have hm := map_list_prod (padAlong (F:=F) e)
    (List.ofFn (fun i => (a i)⁻¹*(b i)⁻¹*a i*b i))
  rw [hab] at hm
  simpa only [List.map_ofFn,Function.comp_def,map_mul,map_inv,orderedProduct,A,B] using hm.symm
end NikolovSegal.PartIISLnDisplacedClassWords
