/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularActions
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularActions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularReconstruction
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace NikolovSegal.PartIIUnitriangularActions
open PartIIUnitriangularLayers
universe u
variable {F : Type u} [Field F] {n : ℕ}

/-- The genuine constant vector on the first superdiagonal. -/
def FirstLayerConstant (a : Matrix.SpecialLinearGroup (Fin n) F) (t : F) : Prop :=
  ∀ i : ℕ, ∀ hi : i+1<n, a ⟨i,by omega⟩ ⟨i+1,hi⟩=t

private theorem adjacent_product (a b : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth 1 (a.val-1)) (hb : LayerDepth 1 (b.val-1))
    (i : ℕ) (hi : i+1<n) :
    (a*b) ⟨i,by omega⟩ ⟨i+1,hi⟩=
      a ⟨i,by omega⟩ ⟨i+1,hi⟩+b ⟨i,by omega⟩ ⟨i+1,hi⟩ := by
  have he : (a*b).val-1=(a.val-1)*(b.val-1)+(a.val-1)+(b.val-1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]; noncomm_ring
  have h0 := (unitLayer% depth_mul) ha hb ⟨i,by omega⟩ ⟨i+1,hi⟩ (by change i+1 < i+(1+1); omega)
  have hij : (⟨i,by omega⟩ : Fin n) ≠ ⟨i+1,hi⟩ := by
    intro h; have hh := congrArg Fin.val h; change i=i+1 at hh; omega
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) F => A ⟨i,by omega⟩ ⟨i+1,hi⟩) he
  simpa only [Matrix.sub_apply,Matrix.add_apply,Matrix.one_apply,if_neg hij,sub_zero,h0,zero_add] using h

private theorem adjacent_inverse (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth 1 (a.val-1)) (i : ℕ) (hi : i+1<n) :
    a⁻¹ ⟨i,by omega⟩ ⟨i+1,hi⟩ = -a ⟨i,by omega⟩ ⟨i+1,hi⟩ := by
  have h := adjacent_product a a⁻¹ ha ((unitLayer% inverse_unit_depth) a ha) i hi
  have hij : (⟨i,by omega⟩ : Fin n) ≠ ⟨i+1,hi⟩ := by
    intro h; have hh := congrArg Fin.val h; change i=i+1 at hh; omega
  simp only [mul_inv_cancel,Matrix.SpecialLinearGroup.coe_one,Matrix.one_apply,if_neg hij] at h
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h.symm)

private theorem first_mul (a b : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth 1 (a.val-1)) (hb : LayerDepth 1 (b.val-1)) (s t : F)
    (has : FirstLayerConstant a s) (hbt : FirstLayerConstant b t) :
    FirstLayerConstant (a*b) (s+t) := by
  intro i hi
  rw [adjacent_product a b ha hb,has i hi,hbt i hi]

private theorem first_inv (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth 1 (a.val-1)) (t : F) (hat : FirstLayerConstant a t) :
    FirstLayerConstant a⁻¹ (-t) := by
  intro i hi
  rw [adjacent_inverse a ha,hat i hi]

/-- Entrywise field action on actual determinant-one matrices, every rank. -/
def fieldAut (phi : RingAut F) : MulAut (Matrix.SpecialLinearGroup (Fin n) F) where
  toFun := Matrix.SpecialLinearGroup.map phi.toRingHom
  invFun := Matrix.SpecialLinearGroup.map phi.symm.toRingHom
  left_inv g := by
    apply Matrix.SpecialLinearGroup.ext; intro i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply]
  right_inv g := by
    apply Matrix.SpecialLinearGroup.ext; intro i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply]
  map_mul' := (Matrix.SpecialLinearGroup.map phi.toRingHom).map_mul

private def torusAction (lambda : Fˣ) (g : Matrix.SpecialLinearGroup (Fin n) F) :
    Matrix.SpecialLinearGroup (Fin n) F :=
  ⟨Matrix.diagonal (fun i => (lambda⁻¹:Fˣ)^i.val : Fin n → F)*g.val*
    Matrix.diagonal (fun i => (lambda:F)^i.val),by
    rw [Matrix.det_mul,Matrix.det_mul,g.prop,mul_one,← Matrix.det_mul,
      Matrix.diagonal_mul_diagonal]
    have he : (fun i : Fin n => ((lambda⁻¹:Fˣ):F)^i.val*(lambda:F)^i.val)=fun _ => 1 := by
      funext i
      rw [← mul_pow]
      simp
    rw [he,Matrix.diagonal_one,Matrix.det_one]⟩

/-- The actual height torus diag(1,lambda^-1,lambda^-2,...), as a GL
conjugation on SL. It has no determinant-root or rank restriction. -/
def heightTorus (lambda : Fˣ) : MulAut (Matrix.SpecialLinearGroup (Fin n) F) where
  toFun := torusAction lambda
  invFun := torusAction lambda⁻¹
  left_inv g := by
    apply Matrix.SpecialLinearGroup.ext; intro i j
    simp only [torusAction,Matrix.diagonal_mul,Matrix.mul_diagonal,inv_inv]
    change ((lambda:F)^i.val*(((lambda⁻¹:Fˣ):F)^i.val*g i j*(lambda:F)^j.val))*((lambda⁻¹:Fˣ):F)^j.val=g i j
    have h1 : (lambda:F)^i.val*((lambda⁻¹:Fˣ):F)^i.val=1 := by rw [← mul_pow]; simp
    have h2 : (lambda:F)^j.val*((lambda⁻¹:Fˣ):F)^j.val=1 := by rw [← mul_pow]; simp
    calc
      _ = ((lambda:F)^i.val*((lambda⁻¹:Fˣ):F)^i.val)*g i j*((lambda:F)^j.val*((lambda⁻¹:Fˣ):F)^j.val) := by ring
      _ = _ := by rw [h1,h2]; simp
  right_inv g := by
    apply Matrix.SpecialLinearGroup.ext; intro i j
    simp only [torusAction,Matrix.diagonal_mul,Matrix.mul_diagonal,inv_inv]
    change (((lambda⁻¹:Fˣ):F)^i.val*((lambda:F)^i.val*g i j*((lambda⁻¹:Fˣ):F)^j.val))*(lambda:F)^j.val=g i j
    have h1 : ((lambda⁻¹:Fˣ):F)^i.val*(lambda:F)^i.val=1 := by rw [← mul_pow]; simp
    have h2 : ((lambda⁻¹:Fˣ):F)^j.val*(lambda:F)^j.val=1 := by rw [← mul_pow]; simp
    calc
      _ = (((lambda⁻¹:Fˣ):F)^i.val*(lambda:F)^i.val)*g i j*(((lambda⁻¹:Fˣ):F)^j.val*(lambda:F)^j.val) := by ring
      _ = _ := by rw [h1,h2]; simp
  map_mul' g h := by
    apply Subtype.ext
    change Matrix.diagonal (fun i : Fin n => ((lambda⁻¹:Fˣ):F)^i.val)*(g.val*h.val)*
      Matrix.diagonal (fun i => (lambda:F)^i.val) =
      (Matrix.diagonal (fun i => ((lambda⁻¹:Fˣ):F)^i.val)*g.val*Matrix.diagonal (fun i => (lambda:F)^i.val))*
      (Matrix.diagonal (fun i => ((lambda⁻¹:Fˣ):F)^i.val)*h.val*Matrix.diagonal (fun i => (lambda:F)^i.val))
    have hi : Matrix.diagonal (fun i : Fin n => (lambda:F)^i.val)*
        Matrix.diagonal (fun i => ((lambda⁻¹:Fˣ):F)^i.val)=1 := by
      rw [Matrix.diagonal_mul_diagonal]
      apply Matrix.diagonal_eq_one.mpr; funext i
      rw [← mul_pow]; simp
    simp only [mul_assoc]
    rw [← mul_assoc (Matrix.diagonal (fun i : Fin n => (lambda:F)^i.val))
      (Matrix.diagonal (fun i => ((lambda⁻¹:Fˣ):F)^i.val)),hi,one_mul]

private theorem torus_entry (lambda : Fˣ) (a : Matrix.SpecialLinearGroup (Fin n) F)
    (i j : Fin n) : (heightTorus lambda a) i j=
      ((lambda⁻¹:Fˣ):F)^i.val*a i j*(lambda:F)^j.val := by
  change (Matrix.diagonal (fun k : Fin n => ((lambda⁻¹:Fˣ):F)^k.val)*a.val*
    Matrix.diagonal (fun k : Fin n => (lambda:F)^k.val)) i j=_
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal]

private theorem torus_depth (lambda : Fˣ) (k : ℕ)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1)) :
    LayerDepth k ((heightTorus lambda a).val-1) := by
  intro i j hij
  have h := ha i j hij
  simp only [Matrix.sub_apply] at h ⊢
  rw [torus_entry,sub_eq_zero.mp h]
  by_cases he : i=j
  · subst j
    simp only [Matrix.one_apply,ite_true,mul_one]
    rw [← mul_pow]; simp
  · simp [Matrix.one_apply,he]

private theorem torus_first (lambda : Fˣ) (a : Matrix.SpecialLinearGroup (Fin n) F)
    (t : F) (ha : FirstLayerConstant a t) :
    FirstLayerConstant (heightTorus lambda a) ((lambda:F)*t) := by
  intro i hi
  rw [torus_entry,ha i hi]
  change ((lambda⁻¹:Fˣ):F)^i*t*(lambda:F)^(i+1)=(lambda:F)*t
  rw [pow_succ]
  have hc : ((lambda⁻¹:Fˣ):F)^i*(lambda:F)^i=1 := by rw [← mul_pow]; simp
  calc
    _ = (((lambda⁻¹:Fˣ):F)^i*(lambda:F)^i)*((lambda:F)*t) := by ring
    _ = _ := by rw [hc,one_mul]

private def reverseTranspose (g : Matrix.SpecialLinearGroup (Fin n) F) :
    Matrix.SpecialLinearGroup (Fin n) F :=
  ⟨Matrix.reindex Fin.revPerm Fin.revPerm g.val.transpose,by
    rw [Matrix.det_reindex_self,Matrix.det_transpose,g.prop]⟩
private theorem reverseTranspose_mul (g h : Matrix.SpecialLinearGroup (Fin n) F) :
    reverseTranspose (g*h)=reverseTranspose h*reverseTranspose g := by
  apply Subtype.ext
  change Matrix.reindex Fin.revPerm Fin.revPerm (g.val*h.val).transpose =
    Matrix.reindex Fin.revPerm Fin.revPerm h.val.transpose *
    Matrix.reindex Fin.revPerm Fin.revPerm g.val.transpose
  rw [Matrix.transpose_mul]
  exact (Matrix.submatrix_mul_equiv h.val.transpose g.val.transpose
    Fin.revPerm.symm Fin.revPerm.symm Fin.revPerm.symm).symm
private theorem reverseTranspose_inv (g : Matrix.SpecialLinearGroup (Fin n) F) :
    reverseTranspose g⁻¹=(reverseTranspose g)⁻¹ := by
  apply Subtype.ext
  change Matrix.reindex Fin.revPerm Fin.revPerm (Matrix.adjugate g.val).transpose =
    Matrix.adjugate (Matrix.reindex Fin.revPerm Fin.revPerm g.val.transpose)
  rw [Matrix.adjugate_reindex,Matrix.adjugate_transpose]
private theorem reverseTranspose_twice (g : Matrix.SpecialLinearGroup (Fin n) F) :
    reverseTranspose (reverseTranspose g)=g := by
  apply Matrix.SpecialLinearGroup.ext; intro i j
  simp [reverseTranspose,Matrix.reindex_apply,Matrix.submatrix_apply,Fin.revPerm]

private def rawGraph : MulAut (Matrix.SpecialLinearGroup (Fin n) F) where
  toFun g := reverseTranspose g⁻¹
  invFun g := reverseTranspose g⁻¹
  left_inv g := by simp only [reverseTranspose_inv,inv_inv,reverseTranspose_twice]
  right_inv g := by simp only [reverseTranspose_inv,inv_inv,reverseTranspose_twice]
  map_mul' g h := by rw [mul_inv_rev,reverseTranspose_mul]

private theorem rawGraph_entry (a : Matrix.SpecialLinearGroup (Fin n) F)
    (i j : Fin n) : rawGraph a i j=a⁻¹ j.rev i.rev := rfl
private theorem rawGraph_depth (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth 1 (a.val-1)) : LayerDepth 1 ((rawGraph a).val-1) := by
  have hi := (unitLayer% inverse_unit_depth) a ha
  intro i j hij
  have hrev : i.rev.val < j.rev.val+1 := by
    simp only [Fin.val_rev]; omega
  have h := hi j.rev i.rev hrev
  simp only [Matrix.sub_apply] at h ⊢
  rw [rawGraph_entry]
  convert h using 1
  simp [Matrix.one_apply,Fin.rev_inj,eq_comm]
private theorem rawGraph_first (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth 1 (a.val-1)) (t : F) (hat : FirstLayerConstant a t) :
    FirstLayerConstant (rawGraph a) (-t) := by
  intro i hi
  rw [rawGraph_entry]
  let k := n-(i+2)
  have hk : k+1<n := by dsimp only [k]; omega
  have h1 : (⟨i+1,hi⟩ : Fin n).rev=⟨k,by omega⟩ := by
    apply Fin.ext; rfl
  have h2 : (⟨i,by omega⟩ : Fin n).rev=⟨k+1,hk⟩ := by
    apply Fin.ext; change n-(i+1)=k+1; dsimp only [k]; omega
  rw [h1,h2,adjacent_inverse a ha,hat k hk]

/-- The pinned positive graph automorphism. The alternating torus corrects
inverse-transpose's first-layer minus signs, so simple roots are permuted
with coefficient +1, exactly as in printed Lemma9.1. -/
def positiveGraph : MulAut (Matrix.SpecialLinearGroup (Fin n) F) :=
  heightTorus (-1:Fˣ)*rawGraph

/-- Actual field/positive-graph action, not a supplied component-law premise. -/
def fieldGraphAut (phi : RingAut F) (eps : Bool) : MulAut (Matrix.SpecialLinearGroup (Fin n) F) :=
  fieldAut phi*(if eps then positiveGraph else 1)

theorem actual_field_graph_first_layer (phi : RingAut F) (eps : Bool)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth 1 (a.val-1))
    (t : F) (hat : FirstLayerConstant a t) :
    LayerDepth 1 ((fieldGraphAut phi eps a).val-1) ∧
      FirstLayerConstant (fieldGraphAut phi eps a) (phi t) := by
  have hf : ∀ b : Matrix.SpecialLinearGroup (Fin n) F,
      LayerDepth 1 (b.val-1) → LayerDepth 1 ((fieldAut phi b).val-1) := by
    intro b hb i j hij
    have hh := hb i j hij
    simp only [Matrix.sub_apply] at hh ⊢
    change phi (b i j)-(1:Matrix (Fin n) (Fin n) F) i j=0
    rw [sub_eq_zero.mp hh]
    simp [Matrix.one_apply]
  have hft : ∀ b : Matrix.SpecialLinearGroup (Fin n) F,
      FirstLayerConstant b t → FirstLayerConstant (fieldAut phi b) (phi t) := by
    intro b hb i hi
    change phi (b ⟨i,by omega⟩ ⟨i+1,hi⟩)=phi t
    rw [hb i hi]
  cases eps
  · simpa only [fieldGraphAut,Bool.false_eq_true,ite_false,mul_one] using ⟨hf a ha,hft a hat⟩
  · have hd := torus_depth (-1:Fˣ) 1 (rawGraph a) (rawGraph_depth a ha)
    have ht := torus_first (-1:Fˣ) (rawGraph a) (-t) (rawGraph_first a ha t hat)
    have ht' : FirstLayerConstant (positiveGraph a) t := by
      change FirstLayerConstant (heightTorus (-1:Fˣ) (rawGraph a)) t
      simpa only [Units.val_neg,Units.val_one,neg_mul,one_mul,neg_neg] using ht
    exact ⟨hf _ hd,hft _ ht'⟩
end NikolovSegal.PartIIUnitriangularActions
