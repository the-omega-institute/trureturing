/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIRadicalInnerTorus
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIOuterBlockConstruction
import Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.OrderOfElement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! Actual type-A D0 Phi Gamma construction, PartII Section2/Section5,
printed pp249--251. Its rank-independent cardinal bound and determinant-one
normal form consume the accepted inner-torus and exact Fin VALUE blocks.
The fixed qth-power class-size/diameter existence is still unproved. -/
namespace NikolovSegal.PartIIOuterSLnAction
open Matrix PartIIUnitriangularActions
universe u
variable {F : Type u} [Field F] {n : ℕ}
private abbrev D (a : Fin n → Fˣ) := (unitOdd% diagonalAut) a
private abbrev G : MulAut (SpecialLinearGroup (Fin n) F) := positiveGraph
private def fieldUnits (phi : RingAut F) (a : Fin n → Fˣ) : Fin n → Fˣ :=
  fun i => Units.mk0 (phi (a i:F)) (by
    intro h
    apply (a i).ne_zero
    exact phi.injective (by simpa only [map_zero] using h))
private def graphUnits (a : Fin n → Fˣ) : Fin n → Fˣ := fun i => (a i.rev)⁻¹
private theorem diagonal_mul (a b : Fin n → Fˣ) : D a*D b=D (a*b) := by
  apply MulEquiv.ext; intro g
  apply SpecialLinearGroup.ext; intro i j
  rw [MulAut.mul_apply,(unitOdd% diagonal_entry),(unitOdd% diagonal_entry),(unitOdd% diagonal_entry)]
  simp only [Pi.mul_apply,Units.val_mul,_root_.mul_inv_rev,Units.val_inv_eq_inv_val]
  ring
private theorem diagonal_one : D (fun _ : Fin n => (1:Fˣ))=1 := by
  apply MulEquiv.ext; intro g
  apply SpecialLinearGroup.ext; intro i j
  simp only [(unitOdd% diagonal_entry),inv_one,Units.val_one,one_mul,mul_one,MulAut.one_apply]
private theorem diagonal_commute (a b : Fin n → Fˣ) : Commute (D a) (D b) := by
  rw [Commute,SemiconjBy,diagonal_mul,diagonal_mul,mul_comm a b]
private theorem field_diagonal (phi : RingAut F) (a : Fin n → Fˣ) :
    fieldAut phi*D a=D (fieldUnits phi a)*fieldAut phi := by
  apply MulEquiv.ext; intro g
  apply SpecialLinearGroup.ext; intro i j
  change phi (((D a) g) i j)=((D (fieldUnits phi a)) (fieldAut phi g)) i j
  rw [(unitOdd% diagonal_entry),(unitOdd% diagonal_entry)]
  change phi ((a i:F)*g i j*((a j)⁻¹:Fˣ))=
    (fieldUnits phi a i:F)*phi (g i j)*((fieldUnits phi a j)⁻¹:Fˣ)
  simp only [fieldUnits,Units.val_inv_eq_inv_val,Units.val_mk0,map_mul,map_inv₀]
private theorem raw_diagonal (a : Fin n → Fˣ) :
    (unitAction% rawGraph)*D a=D (graphUnits a)*(unitAction% rawGraph) := by
  apply MulEquiv.ext; intro g
  apply SpecialLinearGroup.ext; intro i j
  rw [MulAut.mul_apply,(unitAction% rawGraph_entry),← map_inv,(unitOdd% diagonal_entry),
    MulAut.mul_apply,(unitOdd% diagonal_entry),(unitAction% rawGraph_entry)]
  simp only [graphUnits,inv_inv,Units.val_inv_eq_inv_val]
  ring
private theorem height_diagonal : heightTorus (-1:Fˣ)=D (fun i : Fin n => (-1:Fˣ)⁻¹^i.val) := by
  apply MulEquiv.ext; intro g
  apply SpecialLinearGroup.ext; intro i j
  rw [(unitAction% torus_entry),(unitOdd% diagonal_entry)]
  simp only [inv_pow,inv_inv,Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val]
private theorem graph_diagonal (a : Fin n → Fˣ) : G*D a=D (graphUnits a)*G := by
  change (heightTorus (-1:Fˣ)*(unitAction% rawGraph))*D a=
    D (graphUnits a)*(heightTorus (-1:Fˣ)*(unitAction% rawGraph))
  rw [mul_assoc,raw_diagonal,← mul_assoc,height_diagonal,(diagonal_commute _ _).eq,mul_assoc]
private theorem raw_field (phi : RingAut F) :
    ((unitAction% rawGraph) : MulAut (SpecialLinearGroup (Fin n) F))*fieldAut phi=fieldAut phi*(unitAction% rawGraph) := by
  apply MulEquiv.ext; intro g
  apply SpecialLinearGroup.ext; intro i j
  rw [MulAut.mul_apply,(unitAction% rawGraph_entry),← map_inv,MulAut.mul_apply]
  rfl
private theorem graph_field (phi : RingAut F) :
    (G : MulAut (SpecialLinearGroup (Fin n) F))*fieldAut phi=fieldAut phi*G := by
  change (heightTorus (-1:Fˣ)*(unitAction% rawGraph))*fieldAut phi=
    fieldAut phi*(heightTorus (-1:Fˣ)*(unitAction% rawGraph))
  rw [mul_assoc,raw_field,← mul_assoc,height_diagonal]
  have ht : fieldUnits phi (fun i : Fin n => (-1:Fˣ)⁻¹^i.val)=fun i : Fin n => (-1:Fˣ)⁻¹^i.val := by
    funext i
    apply Units.ext
    change phi (((-1:Fˣ)⁻¹^i.val:F))=(((-1:Fˣ)⁻¹^i.val:F))
    simp only [Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val,Units.val_neg,Units.val_one,
      map_pow,map_inv₀,map_neg,map_one]
  rw [← mul_assoc (fieldAut phi),field_diagonal,ht]
private theorem raw_square : (unitAction% rawGraph)*(unitAction% rawGraph)=
    (1 : MulAut (SpecialLinearGroup (Fin n) F)) := by
  apply MulEquiv.ext; intro g
  exact (unitAction% rawGraph).left_inv g
private theorem graph_square : G*G=(1 : MulAut (SpecialLinearGroup (Fin n) F)) := by
  change (heightTorus (-1:Fˣ)*(unitAction% rawGraph))*(heightTorus (-1:Fˣ)*(unitAction% rawGraph))=_
  rw [height_diagonal,mul_assoc,← mul_assoc (unitAction% rawGraph),raw_diagonal,
    mul_assoc (D _),raw_square,mul_one,diagonal_mul]
  have ha : ((fun i : Fin n => (-1:Fˣ)⁻¹^i.val)*
      graphUnits (fun i : Fin n => (-1:Fˣ)⁻¹^i.val))=fun _ : Fin n => (-1:Fˣ)^(n-1) := by
    funext i
    have hneg : (-1:Fˣ)⁻¹=(-1:Fˣ) := by simp
    have hpow : ∀ m : ℕ, ((-1:Fˣ)^m)⁻¹=(-1:Fˣ)^m := by
      intro m
      rw [← _root_.inv_pow,hneg]
    change (-1:Fˣ)⁻¹^i.val*(((-1:Fˣ)⁻¹^i.rev.val)⁻¹)=(-1:Fˣ)^(n-1)
    simp only [hneg,hpow,← pow_add]
    congr 1
    simp only [Fin.val_rev]
    omega
  rw [ha]
  apply MulEquiv.ext; intro g
  apply SpecialLinearGroup.ext; intro i j
  rw [(unitOdd% diagonal_entry)]
  simp [mul_comm,mul_left_comm,mul_assoc]
private def diagram (eps : Bool) : MulAut (SpecialLinearGroup (Fin n) F) :=
  if eps then G else 1
private theorem field_mul (phi psi : RingAut F) :
    fieldAut (n:=n) phi*fieldAut psi=fieldAut (phi*psi) := by
  apply MulEquiv.ext; intro g
  apply SpecialLinearGroup.ext; intro i j
  rfl
private theorem field_one : fieldAut (n:=n) (1:RingAut F)=1 := by
  apply MulEquiv.ext; intro g
  apply SpecialLinearGroup.ext; intro i j
  rfl
private theorem diagram_mul (eps del : Bool) :
    diagram (n:=n) (F:=F) eps*diagram del=diagram (Bool.xor eps del) := by
  cases eps <;> cases del <;> simp only [diagram,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true,one_mul,mul_one,graph_square]
private theorem diagram_diagonal (eps : Bool) (a : Fin n → Fˣ) :
    diagram eps*D a=D (if eps then graphUnits a else a)*diagram eps := by
  cases eps <;> simp only [diagram,Bool.false_eq_true,ite_false,ite_true,one_mul,mul_one,graph_diagonal]
private theorem diagram_field (eps : Bool) (phi : RingAut F) :
    diagram (n:=n) eps*fieldAut phi=fieldAut phi*diagram eps := by
  cases eps <;> simp only [diagram,Bool.false_eq_true,ite_false,ite_true,one_mul,mul_one,graph_field]
/-- Actual D0: only the first and last diagonal coefficients may vary.
It has no determinant-root or bounded-rank premise. -/
def boundaryTorus (k : ℕ) : Subgroup (Fin (k+2) → Fˣ) where
  carrier := {a | ∀ j : Fin k, a (j.castSucc.succ)=1}
  one_mem' := fun _ => rfl
  mul_mem' := by intro a b ha hb j; simp only [Pi.mul_apply,ha j,hb j,one_mul]
  inv_mem' := by intro a ha j; simp only [Pi.inv_apply,ha j,inv_one]
noncomputable instance [Finite F] (k : ℕ) : Fintype (boundaryTorus (F:=F) k) := Fintype.ofFinite _
private def boundary (k : ℕ) (u v : Fˣ) : Fin (k+2) → Fˣ :=
  Fin.cons u (Fin.snoc (fun _ : Fin k => 1) v)
private theorem boundary_mem (k : ℕ) (u v : Fˣ) : boundary k u v∈boundaryTorus (F:=F) k := by
  intro j
  simp only [boundary,Fin.cons_succ,Fin.snoc_castSucc]
private theorem boundary_product (k : ℕ) (u v : Fˣ) : ∏ i, boundary k u v i=u*v := by
  simp only [boundary,Fin.prod_cons,Fin.prod_snoc,Finset.prod_const_one,one_mul]
private theorem field_boundary {k : ℕ} (phi : RingAut F) (a : boundaryTorus (F:=F) k) :
    fieldUnits phi a.val∈boundaryTorus (F:=F) k := by
  intro j
  apply Units.ext
  change phi ((a.val (j.castSucc.succ):F))=(1:F)
  rw [a.prop j]
  exact map_one phi
private theorem graph_boundary {k : ℕ} (a : boundaryTorus (F:=F) k) :
    graphUnits a.val∈boundaryTorus (F:=F) k := by
  intro j
  have hr : (j.castSucc.succ).rev=j.rev.castSucc.succ := by
    apply Fin.ext
    simp only [Fin.val_rev,Fin.val_succ,Fin.val_castSucc]
    omega
  simp only [graphUnits,hr,a.prop j.rev,inv_one]
/-- Actual full determinant-one boundary diagonal/field/positive-graph action. -/
def boundaryAction {k : ℕ} (a : boundaryTorus (F:=F) k) (phi : RingAut F) (eps : Bool) :
    MulAut (SpecialLinearGroup (Fin (k+2)) F) := D a.val*fieldAut phi*diagram eps
private theorem boundaryAction_mul {k : ℕ} (a b : boundaryTorus (F:=F) k)
    (phi psi : RingAut F) (eps del : Bool) :
    ∃ c : boundaryTorus (F:=F) k,
      boundaryAction a phi eps*boundaryAction b psi del=boundaryAction c (phi*psi) (Bool.xor eps del) := by
  let b' : boundaryTorus (F:=F) k :=
    ⟨if eps then graphUnits b.val else b.val,by
      cases eps
      · exact b.prop
      · exact graph_boundary b⟩
  let c : boundaryTorus (F:=F) k := a*⟨fieldUnits phi b'.val,field_boundary phi b'⟩
  refine ⟨c,?_⟩
  change (D a.val*fieldAut phi*diagram eps)*(D b.val*fieldAut psi*diagram del)=
    D c.val*fieldAut (phi*psi)*diagram (Bool.xor eps del)
  calc
    _ = D a.val*(fieldAut phi*(diagram eps*D b.val))*fieldAut psi*diagram del := by group
    _ = D a.val*(fieldAut phi*(D b'.val*diagram eps))*fieldAut psi*diagram del := by rw [diagram_diagonal]
    _ = D a.val*((fieldAut phi*D b'.val)*diagram eps)*fieldAut psi*diagram del := by group
    _ = D a.val*((D (fieldUnits phi b'.val)*fieldAut phi)*diagram eps)*fieldAut psi*diagram del := by rw [field_diagonal]
    _ = (D a.val*D (fieldUnits phi b'.val))*(fieldAut phi*(diagram eps*fieldAut psi))*diagram del := by group
    _ = (D a.val*D (fieldUnits phi b'.val))*(fieldAut phi*(fieldAut psi*diagram eps))*diagram del := by rw [diagram_field]
    _ = (D a.val*D (fieldUnits phi b'.val))*(fieldAut phi*fieldAut psi)*(diagram eps*diagram del) := by group
    _ = _ := by rw [diagonal_mul,field_mul,diagram_mul]; rfl
private theorem boundaryAction_one (k : ℕ) : boundaryAction (1:boundaryTorus (F:=F) k) 1 false=1 := by
  change D (fun _ : Fin (k+2) => (1:Fˣ))*fieldAut (1:RingAut F)*diagram false=1
  simp only [diagram,Bool.false_eq_true,ite_false,diagonal_one,field_one,one_mul,mul_one]
private def normalForms (k : ℕ) : Set (MulAut (SpecialLinearGroup (Fin (k+2)) F)) :=
  {b | ∃ a : boundaryTorus (F:=F) k, ∃ phi : RingAut F, ∃ eps : Bool, b=boundaryAction a phi eps}
private theorem normal_one (k : ℕ) : 1∈normalForms (F:=F) k :=
  ⟨1,1,false,(boundaryAction_one k).symm⟩
private theorem normal_mul (k : ℕ) {b c : MulAut (SpecialLinearGroup (Fin (k+2)) F)}
    (hb : b∈normalForms (F:=F) k) (hc : c∈normalForms (F:=F) k) :
    b*c∈normalForms (F:=F) k := by
  obtain ⟨a,phi,eps,rfl⟩ := hb
  obtain ⟨b,psi,del,rfl⟩ := hc
  obtain ⟨c,he⟩ := boundaryAction_mul a b phi psi eps del
  exact ⟨c,phi*psi,Bool.xor eps del,he⟩
private instance autoFinite [Finite F] (k : ℕ) :
    Finite (MulAut (SpecialLinearGroup (Fin (k+2)) F)) :=
  Finite.of_injective (fun b : MulAut (SpecialLinearGroup (Fin (k+2)) F) =>
    (b : SpecialLinearGroup (Fin (k+2)) F → SpecialLinearGroup (Fin (k+2)) F)) DFunLike.coe_injective
/-- Constructed finite D0 Phi Gamma subgroup, with actual full SL actions.
Inverses are derived from finite order of the concrete automorphism group,
not from a supplied outer-subgroup premise. -/
def finiteOuter [Finite F] (k : ℕ) : Subgroup (MulAut (SpecialLinearGroup (Fin (k+2)) F)) where
  carrier := normalForms (F:=F) k
  one_mem' := normal_one k
  mul_mem' := normal_mul k
  inv_mem' := by
    intro b hb
    have hp : ∀ N : ℕ, b^N∈normalForms (F:=F) k := by
      intro N
      induction N with
      | zero => simpa only [pow_zero] using normal_one (F:=F) k
      | succ N ih => simpa only [pow_succ] using normal_mul k ih hb
    have he : b^(orderOf b-1)*b=1 := by
      rw [← pow_succ,Nat.sub_one_add_one_eq_of_pos (orderOf_pos b),pow_orderOf_eq_one]
    have hi : b⁻¹=b^(orderOf b-1) := by
      calc b⁻¹ = b⁻¹*(b^(orderOf b-1)*b) := by rw [he,mul_one]
           _ = b^(orderOf b-1) := by group
    rw [hi]
    exact hp _
noncomputable instance [Finite F] (k : ℕ) : Fintype (finiteOuter (F:=F) k) := Fintype.ofFinite _
/-- Actual determinant-one normalization of every prescribed DFG entry into
constructed finiteOuter. The correcting matrix and complete action identity
are produced before any targets. No bare automorphism classification is
assumed or inferred from an agreement only on U. -/
theorem actual_DFG_finite_outer_normalization [Finite F] {k : ℕ}
    (a : Fin (k+2) → Fˣ) (phi : RingAut F) (eps : Bool) :
    ∃ h : SpecialLinearGroup (Fin (k+2)) F,
      ∃ b : finiteOuter (F:=F) k,
        PartIIProposition6_5.diagonalFieldGraph a phi eps=MulAut.conj h*(b : MulAut _) := by
  let b : boundaryTorus (F:=F) k := ⟨boundary k (∏ i, a i) 1,boundary_mem k _ _⟩
  obtain ⟨h,hd,he⟩ := PartIIRadicalInnerTorus.actual_diagonal_inner_normalization a b.val
    (by simp only [b,boundary_product,mul_one]) phi eps
  have he' : MulAut.conj h*PartIIProposition6_5.diagonalFieldGraph a phi eps=boundaryAction b phi eps := by
    simpa only [boundaryAction,fieldGraphAut,diagram,mul_assoc] using he
  refine ⟨h⁻¹,⟨boundaryAction b phi eps,b,phi,eps,rfl⟩,?_⟩
  simp only [map_inv,← he']
  group
private theorem boundary_card [Fintype F] (k : ℕ) :
    Fintype.card (boundaryTorus (F:=F) k)≤Fintype.card F^2 := by
  classical
  let f : boundaryTorus (F:=F) k → F×F := fun a => ((a.val 0:F),(a.val (Fin.last (k+1)):F))
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · apply Units.ext
      exact congrArg Prod.fst he
    · refine Fin.lastCases ?_ (fun l => ?_) j
      · apply Units.ext
        simpa only [Fin.succ_last] using congrArg Prod.snd he
      · change a.val (l.castSucc.succ)=b.val (l.castSucc.succ)
        rw [a.prop l,b.prop l]
  have h := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_prod,pow_two] using h
/-- The actual finite D0 Phi Gamma subgroup has a cardinality bound that
is independent of rank. This deliberately uses the elementary |Aut(F)|
bound |F|^|F|, without citing a cyclic-Galois theorem as an oracle. -/
theorem actual_finite_outer_card [Fintype F] (k : ℕ) :
    Fintype.card (finiteOuter (F:=F) k)≤
      Fintype.card F^2*(Fintype.card F^Fintype.card F*2) := by
  classical
  letI : Fintype (RingAut F) := Fintype.ofInjective
    (fun phi : RingAut F => (phi : F → F)) DFunLike.coe_injective
  let f : boundaryTorus (F:=F) k×RingAut F×Bool → finiteOuter (F:=F) k :=
    fun p => ⟨boundaryAction p.1 p.2.1 p.2.2,p.1,p.2.1,p.2.2,rfl⟩
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨a,phi,eps,he⟩ := b.prop
    refine ⟨(a,phi,eps),?_⟩
    apply Subtype.ext
    exact he.symm
  have hAut : Fintype.card (RingAut F)≤Fintype.card F^Fintype.card F := by
    simpa only [Fintype.card_fun] using
      Fintype.card_le_of_injective (fun phi : RingAut F => (phi : F → F)) DFunLike.coe_injective
  have h : Fintype.card (finiteOuter (F:=F) k)≤
      Fintype.card (boundaryTorus (F:=F) k×RingAut F×Bool) := Fintype.card_le_of_surjective f hsurj
  simp only [Fintype.card_prod,Fintype.card_bool] at h
  exact h.trans (Nat.mul_le_mul (boundary_card k) (Nat.mul_le_mul_right 2 hAut))
/-- Rank-independent small-field bound, before any rank or action tuple.
This is a genuine constructed subgroup bound, not a finite-outer premise. -/
theorem actual_finite_outer_small_field_card [Fintype F] (k K : ℕ)
    (hF : Fintype.card F≤K) :
    Fintype.card (finiteOuter (F:=F) k)≤K^2*(K^K*2) := by
  have hK : 0<K := lt_of_lt_of_le Fintype.card_pos hF
  have hp : Fintype.card F^Fintype.card F≤K^K :=
    (Nat.pow_le_pow_left hF _).trans (Nat.pow_le_pow_right hK hF)
  exact (actual_finite_outer_card k).trans
    (Nat.mul_le_mul (Nat.pow_le_pow_left hF 2) (Nat.mul_le_mul_right 2 hp))
/-- Concrete Section5 original DFG VALUE consumer. The rank-independent
outer subgroup, its cardinality and actual determinant-one normalization
are constructed above. Only the fixed-root law is required here; no class
width or full-group coverage is assumed. Corrections precede all genuine
ordinary witnesses and the original q/e powers and order remain exact. -/
theorem actual_small_field_DFG_commutator_values [Fintype F] {k : ℕ}
    (q : ℕ) (hq : 0<q) (K R : ℕ) (hF : Fintype.card F≤K)
    (z : SpecialLinearGroup (Fin (k+2)) F)
    (hz : ∀ a : boundaryTorus (F:=F) k, ∀ phi : RingAut F, ∀ eps : Bool, boundaryAction a phi eps z=z)
    (a : Fin (R*(K^2*(K^K*2))) → Fin (k+2) → Fˣ)
    (phi : Fin (R*(K^2*(K^K*2))) → RingAut F)
    (eps : Fin (R*(K^2*(K^K*2))) → Bool)
    (e : Fin (R*(K^2*(K^K*2))) → ℕ) (he : ∀ i, 0<e i ∧ e i ∣ q) :
    ∃ y : Fin (R*(K^2*(K^K*2))) → SpecialLinearGroup (Fin (k+2)) F,
      ∀ g : Fin R → SpecialLinearGroup (Fin (k+2)) F,
        ∃ c : Fin (R*(K^2*(K^K*2))) → SpecialLinearGroup (Fin (k+2)) F,
          NikolovSegal.orderedProduct (fun i => (c i)⁻¹*
            ((PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i)*
              MulAut.conj (y i)⁻¹)^(q/e i)) (c i))=
          NikolovSegal.orderedProduct (fun r => (g r)⁻¹*z^q*(g r)*(z^q)⁻¹) := by
  classical
  choose h b hb using fun i => actual_DFG_finite_outer_normalization (a i) (phi i) (eps i)
  apply PartIIOuterBlockConstruction.actual_finite_outer_original_power_values
    (finiteOuter (F:=F) k) z _ q hq R (K^2*(K^K*2))
    (actual_finite_outer_small_field_card k K hF) _ h b hb e he
  intro beta
  obtain ⟨a,phi,eps,he⟩ := beta.prop
  rw [he]
  exact hz a phi eps
end NikolovSegal.PartIIOuterSLnAction
