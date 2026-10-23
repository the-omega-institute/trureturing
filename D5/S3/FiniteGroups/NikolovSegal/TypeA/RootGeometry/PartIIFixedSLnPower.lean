/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIFixedSLnPower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIOuterSLnAction
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIISLnBigCellCard
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Matrix.PEquiv
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Logic.Equiv.Fin.Rotate
import Lean.Elab.Tactic.Omega
/-! PartII Section5, printed pp249--251: actual type-A fixed qth powers.
The paper cites [SW] for Lemma5.1. Here the stated type-A power-form
class estimate is proved independently by explicit reflected permutation
matrices, exact centralizer row coordinates, the accepted Uplus chart and
an injective UL big cell. No SW/LS2/class-width/CFSG input is assumed.
The original finite-outer VALUE construction is consumed with original
q/e powers and ONE correction before all witnesses. Full class-width and
all-simple uniform scalar PRODUCT remain unproved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace NikolovSegal.PartIIFixedSLnPower
open Equiv
private def leftIndex (L k : ℕ) : Fin L ↪ Fin (k+4*L+2) where
  toFun i := ⟨2*i.val+1,by omega⟩
  inj' := by intro i j he; apply Fin.ext; have hh := congrArg Fin.val he; dsimp at hh; omega
private noncomputable def leftCycle (q k : ℕ) : Perm (Fin (k+4*(q+1)+2)) :=
  (finCycle (1:Fin (q+1))).viaEmbedding (leftIndex (q+1) k)
private noncomputable def reflected (q k : ℕ) : Perm (Fin (k+4*(q+1)+2)) :=
  Fin.revPerm*leftCycle q k*Fin.revPerm
private noncomputable def paired (q k : ℕ) : Perm (Fin (k+4*(q+1)+2)) :=
  leftCycle q k*reflected q k
private theorem left_fix (q k : ℕ) (x : Fin (k+4*(q+1)+2))
    (hx : 2*(q+1)≤x.val) : leftCycle q k x=x := by
  apply Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i,he⟩
  have hh := congrArg Fin.val he
  change 2*i.val+1=x.val at hh
  omega
private theorem reflected_apply (q k : ℕ) (x : Fin (k+4*(q+1)+2)) :
    reflected q k x=(leftCycle q k x.rev).rev := rfl
private theorem reflected_fix_left (q k : ℕ) (x : Fin (k+4*(q+1)+2))
    (hx : x.val < 2*(q+1)) : reflected q k x=x := by
  rw [reflected_apply,left_fix q k x.rev (by simp only [Fin.val_rev]; omega),Fin.rev_rev]
private theorem cycle_disjoint (q k : ℕ) : Perm.Disjoint (leftCycle q k) (reflected q k) := by
  intro x
  by_cases hx : x.val < 2*(q+1)
  · exact Or.inr (reflected_fix_left q k x hx)
  · exact Or.inl (left_fix q k x (by omega))
private theorem left_parity (q k : ℕ) (x : Fin (k+4*(q+1)+2)) :
    (leftCycle q k x).val%2=x.val%2 := by
  classical
  by_cases hx : x∈Set.range (leftIndex (q+1) k)
  · obtain ⟨i,rfl⟩ := hx
    rw [leftCycle,Perm.viaEmbedding_apply]
    change (2*(finCycle (1:Fin (q+1)) i).val+1)%2=(2*i.val+1)%2
    omega
  · rw [leftCycle,Perm.viaEmbedding_apply_of_notMem _ _ _ hx]
private theorem reflected_parity (q k : ℕ) (x : Fin (k+4*(q+1)+2)) :
    (reflected q k x).val%2=x.val%2 := by
  rw [reflected_apply]
  have hh := left_parity q k x.rev
  simp only [Fin.val_rev] at hh ⊢
  have ht := (leftCycle q k x.rev).isLt
  omega
private theorem paired_parity (q k : ℕ) (x : Fin (k+4*(q+1)+2)) :
    (paired q k x).val%2=x.val%2 :=
  (left_parity q k (reflected q k x)).trans (reflected_parity q k x)
private theorem paired_reflection (q k : ℕ) (x : Fin (k+4*(q+1)+2)) :
    paired q k x.rev=(paired q k x).rev := by
  have hh := congrArg (fun p : Perm (Fin (k+4*(q+1)+2)) => p x.rev) (cycle_disjoint q k).commute.eq
  simpa only [Perm.mul_apply,reflected_apply,Fin.rev_rev,paired] using hh
private theorem paired_sign (q k : ℕ) : Perm.sign (paired q k)=1 := by
  have hr : Perm.sign (reflected q k)=Perm.sign (leftCycle q k) := by
    simp only [reflected,map_mul]
    calc Perm.sign Fin.revPerm*Perm.sign (leftCycle q k)*Perm.sign Fin.revPerm =
        Perm.sign (leftCycle q k)*(Perm.sign Fin.revPerm*Perm.sign Fin.revPerm) := by ac_rfl
         _ = _ := by rw [Int.units_mul_self,mul_one]
  rw [paired,map_mul,hr,Int.units_mul_self]
private theorem paired_left_action (q k : ℕ) (i : Fin (q+1)) :
    paired q k (leftIndex (q+1) k i)=leftIndex (q+1) k (finCycle (1:Fin (q+1)) i) := by
  rw [paired,Perm.mul_apply,reflected_fix_left q k _ (by change 2*i.val+1 < 2*(q+1); omega),
    leftCycle,Perm.viaEmbedding_apply]
private theorem paired_power_left (q k N : ℕ) (i : Fin (q+1)) :
    (paired q k^N) (leftIndex (q+1) k i)=
      leftIndex (q+1) k ((finCycle (1:Fin (q+1))^N) i) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [pow_succ',Perm.mul_apply,ih,paired_left_action,pow_succ',Perm.mul_apply]
private theorem cycle_power (q N : ℕ) (i : Fin (q+1)) :
    (finCycle (1:Fin (q+1))^N) i=i+⟨N%(q+1),Nat.mod_lt _ (by omega)⟩ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ',Perm.mul_apply,ih,finCycle_apply]
    apply Fin.ext
    change ((i.val+N%(q+1))%(q+1)+1%(q+1))%(q+1)=(i.val+(N+1)%(q+1))%(q+1)
    simp only [Nat.mod_add_mod,Nat.add_mod_mod,add_assoc]
private theorem paired_power_moves (q k : ℕ) (hq : 0<q) :
    ∃ x : Fin (k+4*(q+1)+2), (paired q k^q) x≠x := by
  refine ⟨leftIndex (q+1) k 0,?_⟩
  rw [paired_power_left,cycle_power,zero_add]
  intro he
  have hh := (leftIndex (q+1) k).injective he
  have hv := congrArg Fin.val hh
  simp only [Fin.val_mk,Fin.val_zero,Nat.mod_eq_of_lt (Nat.lt_succ_self q)] at hv
  omega


open Matrix PartIIUnitriangularActions
universe u
variable {F : Type u} [Field F]
private def pMatrix {n : ℕ} (sigma : Perm (Fin n)) : Matrix (Fin n) (Fin n) F :=
  sigma.toPEquiv.toMatrix
private theorem pMatrix_entry {n : ℕ} (sigma : Perm (Fin n)) (i j : Fin n) :
    pMatrix (F:=F) sigma i j=if sigma i=j then 1 else 0 := by
  simp only [pMatrix,PEquiv.toMatrix_toPEquiv_eq,Matrix.submatrix_apply,Matrix.one_apply,id_eq]
private theorem pMatrix_mul {n : ℕ} (sigma tau : Perm (Fin n)) :
    pMatrix (F:=F) sigma*pMatrix tau=pMatrix (tau*sigma) := by
  rw [pMatrix,pMatrix,pMatrix,Perm.mul_def,Equiv.toPEquiv_trans,PEquiv.toMatrix_trans]
private theorem pMatrix_one {n : ℕ} : pMatrix (F:=F) (1:Perm (Fin n))=1 := by
  ext i j
  simp only [pMatrix_entry,Perm.one_apply,Matrix.one_apply]
private theorem pMatrix_det {n : ℕ} (sigma : Perm (Fin n)) :
    Matrix.det (pMatrix (F:=F) sigma)=(Perm.sign sigma:ℤˣ) := by
  rw [pMatrix,PEquiv.toMatrix_toPEquiv_eq,Matrix.det_permute,Matrix.det_one,mul_one]
private def slPerm {n : ℕ} (sigma : Perm (Fin n)) (hs : Perm.sign sigma=1) :
    SpecialLinearGroup (Fin n) F := ⟨pMatrix sigma,by rw [pMatrix_det,hs]; simp only [Units.val_one,Int.cast_one]⟩
private theorem slPerm_mul {n : ℕ} (sigma tau : Perm (Fin n))
    (hs : Perm.sign sigma=1) (ht : Perm.sign tau=1) :
    slPerm (F:=F) sigma hs*slPerm tau ht=slPerm (tau*sigma) (by rw [map_mul,ht,hs,mul_one]) := by
  apply Subtype.ext
  exact pMatrix_mul sigma tau
private theorem slPerm_inv {n : ℕ} (sigma : Perm (Fin n)) (hs : Perm.sign sigma=1) :
    (slPerm (F:=F) sigma hs)⁻¹=slPerm sigma⁻¹ (by rw [map_inv,hs,inv_one]) := by
  have he : slPerm (F:=F) sigma hs*slPerm sigma⁻¹ (by rw [map_inv,hs,inv_one])=1 := by
    apply Subtype.ext
    change pMatrix sigma*pMatrix sigma⁻¹=(1:Matrix (Fin n) (Fin n) F)
    rw [pMatrix_mul,inv_mul_cancel,pMatrix_one]
  calc
    _ = (slPerm sigma hs)⁻¹*(slPerm sigma hs*slPerm sigma⁻¹ (by rw [map_inv,hs,inv_one])) := by rw [he,mul_one]
    _ = _ := by group
/-- A characteristic-independent, actual determinant-one permutation
matrix in the D0PhiGamma fixed subgroup. Its two reflected cycles have
length q+1, fix both boundary coordinates, and preserve height parity. -/
noncomputable def fixedElement (q k : ℕ) : SpecialLinearGroup (Fin (k+4*(q+1)+2)) F :=
  slPerm (paired q k) (paired_sign q k)
private theorem fixed_pow (q k d : ℕ) :
    (fixedElement (F:=F) q k)^d=slPerm (paired q k^d) (by rw [map_pow,paired_sign,one_pow]) := by
  induction d with
  | zero => apply Subtype.ext; exact pMatrix_one.symm
  | succ d ih =>
    rw [pow_succ,ih,fixedElement,slPerm_mul]
    congr 1
    exact (pow_succ' _ _).symm
private theorem boundary_coefficient (q k : ℕ)
    (a : PartIIOuterSLnAction.boundaryTorus (F:=F) (k+4*(q+1)))
    (i : Fin (k+4*(q+1)+2)) : a.val (paired q k i)=a.val i := by
  have hz : paired q k 0=0 := by
    rw [paired,Perm.mul_apply,reflected_fix_left q k 0 (by simp),leftCycle]
    apply Perm.viaEmbedding_apply_of_notMem
    rintro ⟨j,hj⟩
    have hh := congrArg Fin.val hj
    change 2*j.val+1=0 at hh
    omega
  have hl : paired q k (Fin.last (k+4*(q+1)+1))=Fin.last (k+4*(q+1)+1) := by
    have hh := paired_reflection q k 0
    simpa only [Fin.rev_zero,hz] using hh
  by_cases h0 : i=0
  · rw [h0,hz]
  by_cases hlast : i=Fin.last (k+4*(q+1)+1)
  · rw [hlast,hl]
  have hi0 : 0 < i.val := by
    by_contra hh
    apply h0
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  have hil : i.val<k+4*(q+1)+1 := by
    by_contra hh
    apply hlast
    apply Fin.ext
    simp only [Fin.val_last]
    have := i.isLt
    omega
  have hp0 : 0 < (paired q k i).val := by
    by_contra hh
    have he : paired q k i=0 := by apply Fin.ext; simp only [Fin.val_zero]; omega
    exact h0 ((paired q k).injective (he.trans hz.symm))
  have hpl : (paired q k i).val<k+4*(q+1)+1 := by
    by_contra hh
    have he : paired q k i=Fin.last (k+4*(q+1)+1) := by
      apply Fin.ext
      simp only [Fin.val_last]
      have := (paired q k i).isLt
      omega
    exact hlast ((paired q k).injective (he.trans hl.symm))
  have hm : ∀ j : Fin (k+4*(q+1)+2), 0 < j.val → j.val<k+4*(q+1)+1 → a.val j=1 := by
    intro j hj0 hjl
    let v : Fin (k+4*(q+1)) := ⟨j.val-1,by omega⟩
    have he : v.castSucc.succ=j := by apply Fin.ext; simp only [Fin.val_succ,Fin.val_castSucc]; dsimp [v];omega
    rw [← he]
    exact a.prop v
  rw [hm i hi0 hil,hm _ hp0 hpl]
/-- The actual full boundary-diagonal, field and positive-graph actions
fix the constructed matrix. No fixed-element law is assumed. -/
theorem actual_fixed_element (q k : ℕ)
    (a : PartIIOuterSLnAction.boundaryTorus (F:=F) (k+4*(q+1)))
    (phi : RingAut F) (eps : Bool) :
    PartIIOuterSLnAction.boundaryAction a phi eps (fixedElement q k)=fixedElement q k := by
  have hfield : fieldAut phi (fixedElement (F:=F) q k)=fixedElement q k := by
    apply SpecialLinearGroup.ext;intro i j
    change phi (pMatrix (paired q k) i j)=pMatrix (paired q k) i j
    rw [pMatrix_entry]
    split <;> simp only [map_one,map_zero]
  have hraw : (unitAction% rawGraph) (fixedElement (F:=F) q k)=fixedElement q k := by
    apply SpecialLinearGroup.ext;intro i j
    rw [(unitAction% rawGraph_entry)]
    change (fixedElement (F:=F) q k)⁻¹ j.rev i.rev=pMatrix (paired q k) i j
    rw [fixedElement,slPerm_inv]
    change pMatrix (paired q k)⁻¹ j.rev i.rev=pMatrix (paired q k) i j
    rw [pMatrix_entry,pMatrix_entry]
    have he : (paired q k)⁻¹ j.rev=i.rev ↔ paired q k i=j := by
      change (paired q k).symm j.rev=i.rev ↔ paired q k i=j
      rw [Equiv.symm_apply_eq,paired_reflection,Fin.rev_inj]
      exact eq_comm
    simp only [he]
  have htorus : heightTorus (-1:Fˣ) (fixedElement (F:=F) q k)=fixedElement q k := by
    apply SpecialLinearGroup.ext;intro i j
    rw [(unitAction% torus_entry)]
    change (((-1:Fˣ)⁻¹:Fˣ):F)^i.val*pMatrix (paired q k) i j*((-1:Fˣ):F)^j.val=pMatrix (paired q k) i j
    rw [pMatrix_entry]
    split
    · rename_i hij
      rw [← hij]
      have hp := paired_parity q k i
      have hi : (((-1:Fˣ)⁻¹:Fˣ):F)=(-1:F) := by simp
      rw [hi,mul_one]
      simp only [Units.val_neg,Units.val_one]
      rw [← pow_add]
      have hd : 2∣i.val+(paired q k i).val := by omega
      obtain ⟨d,hd⟩ := hd
      rw [hd,pow_mul]
      simp only [neg_one_sq,one_pow]
    · simp only [mul_zero,zero_mul]
  have hgraph : positiveGraph (fixedElement (F:=F) q k)=fixedElement q k := by
    change heightTorus (-1:Fˣ) ((unitAction% rawGraph) (fixedElement q k))=fixedElement q k
    rw [hraw,htorus]
  have hd : (unitOdd% diagonalAut) a.val (fixedElement (F:=F) q k)=fixedElement q k := by
    apply SpecialLinearGroup.ext;intro i j
    rw [(unitOdd% diagonal_entry)]
    change (a.val i:F)*pMatrix (paired q k) i j*((a.val j)⁻¹:Fˣ)=pMatrix (paired q k) i j
    rw [pMatrix_entry]
    split
    · rename_i hij
      rw [← hij,boundary_coefficient]
      simpa only [mul_one,← Units.val_mul,mul_inv_cancel,Units.val_one]
    · simp only [mul_zero,zero_mul]
  cases eps
  · change (unitOdd% diagonalAut) a.val (fieldAut phi (fixedElement q k))=fixedElement q k
    rw [hfield,hd]
  · change (unitOdd% diagonalAut) a.val (fieldAut phi (positiveGraph (fixedElement q k)))=fixedElement q k
    rw [hgraph,hfield,hd]
/-- Its qth power is nonidentity for EVERY positive q, independently of
characteristic. This does not assert the still-missing large-class bound. -/
theorem actual_fixed_power_nonidentity (q k : ℕ) (hq : 0<q) :
    (fixedElement (F:=F) q k)^q≠1 := by
  obtain ⟨x,hx⟩ := paired_power_moves q k hq
  intro he
  have hh := congrArg (fun g : SpecialLinearGroup (Fin (k+4*(q+1)+2)) F => g x ((paired q k^q) x)) he
  rw [fixed_pow] at hh
  change pMatrix (paired q k^q) x ((paired q k^q) x)=(1:Matrix (Fin (k+4*(q+1)+2)) (Fin (k+4*(q+1)+2)) F) x ((paired q k^q) x) at hh
  simp only [pMatrix_entry,ite_true,Matrix.one_apply,if_neg hx.symm] at hh
  exact one_ne_zero hh
/-- The qth power is genuinely noncentral, not merely nonidentity. -/
theorem actual_fixed_power_noncentral (q k : ℕ) (hq : 0 < q) :
    (fixedElement (F:=F) q k)^q∉Subgroup.center _ := by
  obtain ⟨x,hx⟩ := paired_power_moves q k hq
  intro hc
  have hs := SpecialLinearGroup.scalar_eq_self_of_mem_center hc x
  have hh := congrArg (fun A : Matrix (Fin (k+4*(q+1)+2)) (Fin (k+4*(q+1)+2)) F => A x ((paired q k^q) x)) hs
  change (Matrix.scalar (Fin (k+4*(q+1)+2)) (((fixedElement (F:=F) q k)^q) x x)) x ((paired q k^q) x)=((fixedElement q k)^q) x ((paired q k^q) x) at hh
  rw [fixed_pow] at hh
  change (Matrix.scalar (Fin (k+4*(q+1)+2)) (pMatrix (paired q k^q) x x)) x ((paired q k^q) x)=pMatrix (paired q k^q) x ((paired q k^q) x) at hh
  simp only [Matrix.scalar_apply,Matrix.diagonal_apply,if_neg hx.symm,pMatrix_entry,ite_true] at hh
  exact zero_ne_one hh
/-- Actual original selected Fin/q-over-e VALUE construction in the
small-field branch, now with a constructed fixed element and noncentral
qth power. The rank-independent finite-outer bound and ONE correction
are genuine. This is VALUE range, not the unproved uniform class width. -/
theorem actual_small_field_fixed_power_values [Fintype F]
    (q : ℕ) (hq : 0 < q) (k K R : ℕ) (hF : Fintype.card F≤K)
    (a : Fin (R*(K^2*(K^K*2))) → Fin (k+4*(q+1)+2) → Fˣ)
    (phi : Fin (R*(K^2*(K^K*2))) → RingAut F)
    (eps : Fin (R*(K^2*(K^K*2))) → Bool)
    (e : Fin (R*(K^2*(K^K*2))) → ℕ) (he : ∀ i, 0<e i ∧ e i∣q) :
    ∃ y : Fin (R*(K^2*(K^K*2))) → SpecialLinearGroup (Fin (k+4*(q+1)+2)) F,
      ∀ g : Fin R → SpecialLinearGroup (Fin (k+4*(q+1)+2)) F,
        ∃ c : Fin (R*(K^2*(K^K*2))) → SpecialLinearGroup (Fin (k+4*(q+1)+2)) F,
          NikolovSegal.orderedProduct (fun i => (c i)⁻¹*
            ((PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i)*
              MulAut.conj (y i)⁻¹)^(q/e i)) (c i))=
          NikolovSegal.orderedProduct (fun r => (g r)⁻¹*(fixedElement q k)^q*(g r)*((fixedElement q k)^q)⁻¹) := by
  exact PartIIOuterSLnAction.actual_small_field_DFG_commutator_values q hq K R hF
    (fixedElement q k) (actual_fixed_element q k) a phi eps e he

private theorem paired_period (p k : ℕ) : paired p k^(p+1)=1 := by
  have hc : finCycle (1:Fin (p+1))^(p+1)=1 := by
    ext i
    rw [cycle_power]
    simp only [Nat.mod_self,Fin.zero_eta,add_zero,Perm.one_apply]
  have hl : leftCycle p k^(p+1)=1 := by
    change (Perm.viaEmbeddingHom (leftIndex (p+1) k) (finCycle (1:Fin (p+1))))^(p+1)=1
    rw [← map_pow,hc,map_one]
  have hr : (Fin.revPerm : Perm (Fin (k+4*(p+1)+2)))⁻¹=Fin.revPerm := Fin.revPerm_symm
  have ht : reflected p k^(p+1)=1 := by
    change (Fin.revPerm*leftCycle p k*Fin.revPerm)^(p+1)=1
    have he : Fin.revPerm*leftCycle p k*Fin.revPerm=Fin.revPerm*leftCycle p k*Fin.revPerm⁻¹ := by rw [hr]
    rw [he,_root_.conj_pow,hl,mul_one,mul_inv_cancel]
  change (leftCycle p k*reflected p k)^(p+1)=1
  rw [(cycle_disjoint p k).commute.mul_pow,hl,ht,one_mul]
private theorem fixed_period (p k : ℕ) : (fixedElement (F:=F) p k)^(p+1)=1 := by
  rw [fixed_pow]
  apply Subtype.ext
  change pMatrix (paired p k^(p+1))=(1:Matrix (Fin (k+4*(p+1)+2)) (Fin (k+4*(p+1)+2)) F)
  rw [paired_period,pMatrix_one]
private theorem power_inverse (q r k : ℕ) :
    ((fixedElement (F:=F) (q*r) k)^q)^r=(fixedElement (q*r) k)⁻¹ := by
  have he : ((fixedElement (F:=F) (q*r) k)^q)^r*fixedElement (q*r) k=1 := by
    rw [← pow_mul,← pow_succ,fixed_period]
  calc
    _ = (((fixedElement (F:=F) (q*r) k)^q)^r*fixedElement (q*r) k)*(fixedElement (q*r) k)⁻¹ := by group
    _ = _ := by rw [he,one_mul]
private def leftRows (p k : ℕ) : Finset (Fin (k+4*(p+1)+2)) :=
  Finset.univ.image (leftIndex (p+1) k)
private def rightRows (p k : ℕ) : Finset (Fin (k+4*(p+1)+2)) :=
  (leftRows p k).image Fin.rev
private def rootRows (p k : ℕ) : Finset (Fin (k+4*(p+1)+2)) :=
  (Finset.univ\(leftRows p k∪rightRows p k))∪
    {leftIndex (p+1) k 0,(leftIndex (p+1) k 0).rev}
private theorem rows_disjoint (p k : ℕ) : Disjoint (leftRows p k) (rightRows p k) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hy
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hj
  have hh := congrArg Fin.val he
  change (k+4*(p+1)+2)-(2*v.val+1+1)=2*i.val+1 at hh
  have := i.isLt
  have := v.isLt
  omega
private theorem rootRows_card (p k : ℕ) :
    (rootRows p k).card≤(k+4*(p+1)+2)-2*(p+1)+2 := by
  classical
  have hl : (leftRows p k).card=p+1 := by
    rw [leftRows,Finset.card_image_of_injective _ (leftIndex (p+1) k).injective,
      Finset.card_univ,Fintype.card_fin]
  have hr : (rightRows p k).card=p+1 := by
    rw [rightRows,Finset.card_image_of_injective _ (fun _ _ h => Fin.rev_inj.mp h),hl]
  have hboth : (leftRows p k∪rightRows p k).card=2*(p+1) := by
    rw [Finset.card_union_of_disjoint (rows_disjoint p k),hl,hr]
    omega
  have hbound := Finset.card_union_le
    (Finset.univ\(leftRows p k∪rightRows p k))
    ({leftIndex (p+1) k 0,(leftIndex (p+1) k 0).rev}:Finset _)
  have hp : ({leftIndex (p+1) k 0,(leftIndex (p+1) k 0).rev}:Finset _).card≤2 := by
    exact (Finset.card_insert_le _ _).trans (by simp)
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,hboth] at hbound
  exact hbound.trans (Nat.add_le_add_left hp _)
private theorem paired_reflection_power (p k d : ℕ) (x : Fin (k+4*(p+1)+2)) :
    (paired p k^d) x.rev=((paired p k^d) x).rev := by
  induction d with
  | zero => rfl
  | succ d ih => rw [pow_succ',Perm.mul_apply,Perm.mul_apply,ih,paired_reflection]
private theorem rootRows_reach (p k : ℕ) (i : Fin (k+4*(p+1)+2)) :
    ∃ b∈rootRows p k, ∃ d : ℕ, (paired p k^d) b=i := by
  classical
  by_cases hl : i∈leftRows p k
  · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hl
    refine ⟨leftIndex (p+1) k 0,Finset.mem_union_right _ (by simp),v.val,?_⟩
    rw [paired_power_left,cycle_power,zero_add]
    congr 1
    apply Fin.ext
    exact Nat.mod_eq_of_lt v.isLt
  by_cases hr : i∈rightRows p k
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
    refine ⟨(leftIndex (p+1) k 0).rev,Finset.mem_union_right _ (by simp),w.val,?_⟩
    rw [paired_reflection_power,paired_power_left,cycle_power,zero_add]
    congr 2
    apply Fin.ext
    exact Nat.mod_eq_of_lt w.isLt
  · refine ⟨i,Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩),0,rfl⟩
    simpa only [Finset.mem_union,not_or] using And.intro hl hr
private theorem commuting_rows (p k : ℕ)
    (g : SpecialLinearGroup (Fin (k+4*(p+1)+2)) F)
    (hg : Commute g (fixedElement p k)) (i j : Fin (k+4*(p+1)+2)) :
    g (paired p k i) (paired p k j)=g i j := by
  have hh := congrArg (fun a : SpecialLinearGroup (Fin (k+4*(p+1)+2)) F => a i (paired p k j)) hg.eq
  change (g.val*pMatrix (F:=F) (paired p k)) i (paired p k j)=
    (pMatrix (F:=F) (paired p k)*g.val) i (paired p k j) at hh
  rw [pMatrix,PEquiv.mul_toMatrix_toPEquiv,PEquiv.toMatrix_toPEquiv_mul] at hh
  simpa only [Matrix.submatrix_apply,Equiv.symm_apply_apply,id_eq] using hh.symm
private theorem commuting_rows_power (p k d : ℕ)
    (g : SpecialLinearGroup (Fin (k+4*(p+1)+2)) F)
    (hg : Commute g (fixedElement p k)) (i j : Fin (k+4*(p+1)+2)) :
    g ((paired p k^d) i) ((paired p k^d) j)=g i j := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [pow_succ',Perm.mul_apply,Perm.mul_apply,commuting_rows p k g hg,ih]
/-- Actual centralizer coordinates: every row of a commuting matrix is
reconstructed from the two long-cycle base rows and untouched rows.
This derives an injection; no centralizer-size estimate is assumed. -/
theorem actual_fixed_centralizer_card [Fintype F] (p k : ℕ) :
    Nat.card (Subgroup.centralizer {fixedElement (F:=F) p k})≤
      Fintype.card F^(((k+4*(p+1)+2)-2*(p+1)+2)*(k+4*(p+1)+2)) := by
  classical
  let A := Subgroup.centralizer {fixedElement (F:=F) p k}
  let f : A → (rootRows p k) → Fin (k+4*(p+1)+2) → F := fun g i j => g.val i.val j
  have hinj : Function.Injective f := by
    intro a b he
    have ha : Commute a.val (fixedElement p k) := by
      have hh := a.prop (fixedElement p k) (by simp)
      exact hh.symm
    have hb : Commute b.val (fixedElement p k) := by
      have hh := b.prop (fixedElement p k) (by simp)
      exact hh.symm
    apply Subtype.ext
    apply SpecialLinearGroup.ext
    intro i j
    obtain ⟨v,hv,d,hd⟩ := rootRows_reach p k i
    let w := (paired p k^d)⁻¹ j
    have hj : (paired p k^d) w=j := (paired p k^d).apply_symm_apply j
    rw [← hd,← hj,commuting_rows_power p k d a.val ha,
      commuting_rows_power p k d b.val hb]
    exact congrFun (congrFun he ⟨v,hv⟩) w
  have hh := Nat.card_le_card_of_injective f hinj
  have hh' : Nat.card A≤Fintype.card F^((rootRows p k).card*(k+4*(p+1)+2)) := by
    simpa only [Nat.card_fun,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,← pow_mul,mul_comm] using hh
  exact hh'.trans (Nat.pow_le_pow_right Fintype.card_pos (Nat.mul_le_mul_right _ (rootRows_card p k)))
/-- Coprimality is implemented by (z^q)^r=z^-1 for a cycle of length
qr+1. Thus the ACTUAL qth-power centralizer has the same row bound. -/
theorem actual_q_power_centralizer_card [Fintype F] (q r k : ℕ) :
    Nat.card (Subgroup.centralizer {(fixedElement (F:=F) (q*r) k)^q})≤
      Fintype.card F^(((k+4*(q*r+1)+2)-2*(q*r+1)+2)*(k+4*(q*r+1)+2)) := by
  have hle : Subgroup.centralizer {(fixedElement (F:=F) (q*r) k)^q}≤
      Subgroup.centralizer {fixedElement (q*r) k} := by
    intro a ha
    have hc : Commute a ((fixedElement (F:=F) (q*r) k)^q) :=
      (ha _ (by simp)).symm
    have hi : Commute a (fixedElement (F:=F) (q*r) k) := by
      have hh := hc.pow_right r
      rw [power_inverse] at hh
      simpa only [inv_inv] using hh.inv_right
    intro b hb
    obtain rfl := Set.mem_singleton_iff.mp hb
    exact hi.eq.symm
  exact (Nat.card_le_card_of_injective (fun a => (⟨a.val,hle a.prop⟩ : Subgroup.centralizer {fixedElement (F:=F) (q*r) k}))
    (fun a b h => by
      apply Subtype.ext
      exact congrArg (fun v : Subgroup.centralizer {fixedElement (F:=F) (q*r) k} => v.val) h)).trans (actual_fixed_centralizer_card (q*r) k)

/-- Quantitative actual conjugacy class of the fixed qth power. The
centralizer rows and genuine UL big-cell lower bound give this estimate;
no SW/LS2 power-class or class-width theorem is assumed. -/
theorem actual_q_power_class_lower [Fintype F] (q r k : ℕ) (hp : 1≤q*r) :
    Fintype.card F^((k+4*(q*r+1)+2)*(2*(q*r+1)-3))≤
      Nat.card (ConjClasses.mk ((fixedElement (F:=F) (q*r) k)^q)).carrier := by
  classical
  let n := k+4*(q*r+1)+2
  let z := (fixedElement (F:=F) (q*r) k)^q
  let C := Subgroup.centralizer {z}
  let B := (n-2*(q*r+1)+2)*n
  let E := n*(2*(q*r+1)-3)
  letI : Fintype (ConjClasses.mk z).carrier := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer (ConjAct (SpecialLinearGroup (Fin n) F)) z) := Fintype.ofFinite _
  have he : Nat.card (ConjClasses.mk z).carrier*Nat.card C=Nat.card (SpecialLinearGroup (Fin n) F) := by
    rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]
    simp only [Nat.card_eq_fintype_card]
    rw [ConjClasses.card_carrier]
    apply Nat.div_mul_cancel
    have hd := (MulAction.stabilizer (ConjAct (SpecialLinearGroup (Fin n) F)) z).card_subgroup_dvd_card
    have hc : Nat.card (ConjAct (SpecialLinearGroup (Fin n) F))=Nat.card (SpecialLinearGroup (Fin n) F) :=
      Nat.card_congr ConjAct.ofConjAct.toEquiv
    rw [hc] at hd
    simpa only [Nat.card_eq_fintype_card] using hd
  have hC : Nat.card C≤Fintype.card F^B := actual_q_power_centralizer_card q r k
  have hu : Nat.card (SpecialLinearGroup (Fin n) F)≤Nat.card (ConjClasses.mk z).carrier*Fintype.card F^B := by
    rw [← he]
    exact Nat.mul_le_mul_left _ hC
  have hb := (PartIISLnBigCellCard.actual_SLn_card_lower (F:=F) n).trans hu
  have hn : (n-2*(q*r+1)+2)+(2*(q*r+1)-3)=n-1 := by dsimp [n];omega
  have ha : n*(n-1)=E+B := by
    rw [← hn]
    dsimp only [E,B]
    ring
  rw [ha,pow_add] at hb
  exact Nat.le_of_mul_le_mul_right hb (pow_pos Fintype.card_pos B)
private theorem SLn_card_upper [Fintype F] (n : ℕ) :
    Nat.card (SpecialLinearGroup (Fin n) F)≤Fintype.card F^(n*n) := by
  have h := Nat.card_le_card_of_injective
    (fun g : SpecialLinearGroup (Fin n) F => g.val) Subtype.coe_injective
  change Nat.card (SpecialLinearGroup (Fin n) F)≤Nat.card (Fin n → Fin n → F) at h
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin,← pow_mul] using h
/-- An elementary type-A Lemma5.1 bound in power form: when qr>=k+2,
|SLn(F)|<=|class(z^q)|^8, with z fixed by the constructed D0PhiGamma.
The class-width theorem is a separate, still-unproved obligation. -/
theorem actual_q_power_large_class [Fintype F] (q r k : ℕ) (hp : k+2≤q*r) :
    Nat.card (SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F)≤
      (Nat.card (ConjClasses.mk ((fixedElement (F:=F) (q*r) k)^q)).carrier)^8 := by
  let n := k+4*(q*r+1)+2
  let E := n*(2*(q*r+1)-3)
  have h1 : 1≤q*r := by omega
  have hclass := actual_q_power_class_lower (F:=F) q r k h1
  have hnum : n≤8*(2*(q*r+1)-3) := by dsimp [n];omega
  have hmul : n*n≤E*8 := by
    have hh := Nat.mul_le_mul_left n hnum
    convert hh using 1 <;> dsimp [E] <;> ring
  calc
    _ ≤ Fintype.card F^(n*n) := SLn_card_upper n
    _ ≤ Fintype.card F^(E*8) := Nat.pow_le_pow_right Fintype.card_pos hmul
    _ = (Fintype.card F^E)^8 := pow_mul _ _ _
    _ ≤ _ := Nat.pow_le_pow_left hclass 8
/-- Section5's actual long-cycle VALUE consumer, with the quantitative
class estimate conjoined and the fixed-element law PROVED. R remains the
number of desired ordinary VALUES; uniform class width is not assumed. -/
theorem actual_small_field_large_class_values [Fintype F]
    (q : ℕ) (hq : 0 < q) (r k K R : ℕ) (hp : k+2≤q*r) (hF : Fintype.card F≤K)
    (a : Fin (R*(K^2*(K^K*2))) → Fin (k+4*(q*r+1)+2) → Fˣ)
    (phi : Fin (R*(K^2*(K^K*2))) → RingAut F)
    (eps : Fin (R*(K^2*(K^K*2))) → Bool)
    (e : Fin (R*(K^2*(K^K*2))) → ℕ) (he : ∀ i, 0<e i ∧ e i∣q) :
    Nat.card (SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F)≤
      (Nat.card (ConjClasses.mk ((fixedElement (F:=F) (q*r) k)^q)).carrier)^8 ∧
    ∃ y : Fin (R*(K^2*(K^K*2))) → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
      ∀ g : Fin R → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
        ∃ c : Fin (R*(K^2*(K^K*2))) → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
          NikolovSegal.orderedProduct (fun i => (c i)⁻¹*
            ((PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i)*
              MulAut.conj (y i)⁻¹)^(q/e i)) (c i))=
          NikolovSegal.orderedProduct (fun i => (g i)⁻¹*(fixedElement (q*r) k)^q*(g i)*((fixedElement (q*r) k)^q)⁻¹) := by
  exact ⟨actual_q_power_large_class q r k hp,
    PartIIOuterSLnAction.actual_small_field_DFG_commutator_values q hq K R hF
      (fixedElement (q*r) k) (actual_fixed_element (q*r) k) a phi eps e he⟩

private theorem rank_decomposition (q : ℕ) (hq : 0 < q) (n : ℕ) (hn : 24*q+6≤n) :
    ∃ r k : ℕ, n=k+4*(q*r+1)+2 ∧ k+2≤q*r := by
  let r := (n-6)/(4*q)
  let k := (n-6)%(4*q)
  have hden : 0 < 4*q := by omega
  have hr : 6≤r := (Nat.le_div_iff_mul_le hden).mpr (by omega)
  have hk : k<4*q := Nat.mod_lt _ hden
  have hp : k+2≤q*r := by
    have hh := Nat.mul_le_mul_left q hr
    omega
  have hs : n=k+4*(q*r+1)+2 := by
    have hm := Nat.mod_add_div (n-6) (4*q)
    dsimp only [r,k]
    have hsub : n-6+6=n := Nat.sub_add_cancel (by omega)
    nlinarith [hsub]
  exact ⟨r,k,hs,hp⟩
/-- All sufficiently large actual ranks, with no rank congruence premise.
The Euclidean decomposition constructs the two long cycles; z and its
large qth-power class are chosen before EVERY boundary DFG action. -/
theorem actual_all_large_rank_fixed_power [Fintype F] (q : ℕ) (hq : 0 < q)
    (n : ℕ) (hn : 24*q+6≤n) :
    ∃ z : SpecialLinearGroup (Fin n) F,
      Nat.card (SpecialLinearGroup (Fin n) F)≤(Nat.card (ConjClasses.mk (z^q)).carrier)^8 ∧
      ∀ a : Fin n → Fˣ, (∀ i : Fin n, 0 < i.val → i.val+1<n → a i=1) →
        ∀ phi : RingAut F, ∀ eps : Bool,
          PartIIProposition6_5.diagonalFieldGraph a phi eps z=z := by
  obtain ⟨r,k,rfl,hp⟩ := rank_decomposition q hq n hn
  refine ⟨fixedElement (q*r) k,actual_q_power_large_class q r k hp,?_⟩
  intro a ha phi eps
  let b : PartIIOuterSLnAction.boundaryTorus (F:=F) (k+4*(q*r+1)) :=
    ⟨a,fun j => ha (j.castSucc.succ) (by simp) (by simp only [Fin.val_succ,Fin.val_castSucc];have := j.isLt;omega)⟩
  have hh := actual_fixed_element (q*r) k b phi eps
  cases eps
  · change (unitOdd% diagonalAut) a (fieldAut phi (fixedElement (q*r) k))=fixedElement (q*r) k at hh ⊢
    exact hh
  · change (unitOdd% diagonalAut) a (fieldAut phi (positiveGraph (fixedElement (q*r) k)))=fixedElement (q*r) k at hh ⊢
    exact hh
end NikolovSegal.PartIIFixedSLnPower
