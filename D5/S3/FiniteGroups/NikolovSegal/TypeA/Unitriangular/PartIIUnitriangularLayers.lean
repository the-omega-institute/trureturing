/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option maxHeartbeats 1000000
/-! Nikolov--Segal Part II p264 equation(13): the actual leading matrix
commutator map of a proper unitriangular matrix. This is the rank-independent
linear kernel needed by Proposition6.5, not full U coverage. -/
namespace NikolovSegal.PartIIUnitriangularLayers
universe u
variable {F : Type u} [Field F] {n : ℕ}
/-- Literal kth superdiagonal matrix, with every other entry zero. -/
def layerStrip (k : ℕ) (x : Fin n → F) : Matrix (Fin n) (Fin n) F :=
  fun i j => if j.val=i.val+k then x i else 0
private theorem layer_mul_next (k : ℕ) (i : ℕ) (hi : i+k+1<n)
    (x : Fin n → F) (g : Matrix (Fin n) (Fin n) F) :
    (layerStrip k x*g) ⟨i,by omega⟩ ⟨i+k+1,hi⟩=
      x ⟨i,by omega⟩*g ⟨i+k,by omega⟩ ⟨i+k+1,hi⟩ := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (⟨i+k,by omega⟩ : Fin n)]
  · simp [layerStrip]
  · intro j hj hne
    have hjne : j.val ≠ i+k := by intro h; apply hne; exact Fin.ext h
    simp [layerStrip,hjne]
  · simp
private theorem mul_layer_next (k : ℕ) (i : ℕ) (hi : i+k+1<n)
    (x : Fin n → F) (g : Matrix (Fin n) (Fin n) F) :
    (g*layerStrip k x) ⟨i,by omega⟩ ⟨i+k+1,hi⟩=
      g ⟨i,by omega⟩ ⟨i+1,by omega⟩*x ⟨i+1,by omega⟩ := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (⟨i+1,by omega⟩ : Fin n)]
  · simp [layerStrip,show i+k+1=i+1+k by omega]
  · intro j hj hne
    have hjne : i+k+1 ≠ j.val+k := by intro h; apply hne; apply Fin.ext; change j.val=i+1; omega
    simp [layerStrip,hjne]
  · simp
/-- Actual matrix Lie commutator, preserving the genuine two unequal
coefficients and their order. No constant-coefficient or graph hypothesis. -/
theorem actual_layer_bracket_coordinate (k : ℕ) (i : ℕ) (hi : i+k+1<n)
    (x : Fin n → F) (g : Matrix (Fin n) (Fin n) F) :
    (layerStrip k x*g-g*layerStrip k x) ⟨i,by omega⟩ ⟨i+k+1,hi⟩=
      x ⟨i,by omega⟩*g ⟨i+k,by omega⟩ ⟨i+k+1,hi⟩-
        g ⟨i,by omega⟩ ⟨i+1,by omega⟩*x ⟨i+1,by omega⟩ := by
  rw [Matrix.sub_apply,layer_mul_next,mul_layer_next]
private def layerSolution (a b t : ℕ → F) : ℕ → F
  | 0 => 0
  | i+1 => (layerSolution a b t i*b i-t i)/(a i)
/-- Every prescribed next-layer coordinate is realized by the ACTUAL
matrix commutator with a proper matrix. The recursively solved strip is
one layer wide; the bound/length does not depend on n. This proves the
surjectivity of the printed linear kernel before its group-filtration use. -/
theorem actual_proper_layer_bracket_surjective (k : ℕ)
    (g : Matrix (Fin n) (Fin n) F)
    (hproper : ∀ i : ℕ, ∀ hi : i+1<n, g ⟨i,by omega⟩ ⟨i+1,hi⟩ ≠ 0)
    (target : Fin (n-(k+1)) → F) :
    ∃ x : Fin n → F, ∀ i : Fin (n-(k+1)),
      (layerStrip k x*g-g*layerStrip k x) ⟨i.val,by omega⟩ ⟨i.val+k+1,by omega⟩=target i := by
  classical
  let a : ℕ → F := fun i => if h : i+1<n then g ⟨i,by omega⟩ ⟨i+1,h⟩ else 1
  let b : ℕ → F := fun i => if h : i+k+1<n then g ⟨i+k,by omega⟩ ⟨i+k+1,h⟩ else 0
  let t : ℕ → F := fun i => if h : i<n-(k+1) then target ⟨i,h⟩ else 0
  let x : Fin n → F := fun i => layerSolution a b t i.val
  refine ⟨x,?_⟩
  intro i
  rw [actual_layer_bracket_coordinate]
  have hi : i.val+k+1<n := by omega
  have hi' : i.val+1<n := by omega
  have ha := hproper i.val hi'
  change layerSolution a b t i.val*g ⟨i.val+k,by omega⟩ ⟨i.val+k+1,hi⟩-
    g ⟨i.val,by omega⟩ ⟨i.val+1,hi'⟩*layerSolution a b t (i.val+1)=target i
  rw [layerSolution]
  simp only [a,b,t,dif_pos hi,dif_pos hi',dif_pos i.isLt]
  field_simp
  ring


/-- Literal matrix height filtration used in printed equation(13). -/
def LayerDepth (k : ℕ) (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j, j.val < i.val+k → A i j=0
private theorem depth_mono {k l : ℕ} {A : Matrix (Fin n) (Fin n) F}
    (h : LayerDepth l A) (hkl : k ≤ l) : LayerDepth k A := by
  intro i j hij
  exact h i j (by omega)
private theorem depth_neg {k : ℕ} {A : Matrix (Fin n) (Fin n) F}
    (h : LayerDepth k A) : LayerDepth k (-A) := by
  intro i j hij
  simp only [Matrix.neg_apply,h i j hij,neg_zero]
private theorem depth_add {k : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (ha : LayerDepth k A) (hb : LayerDepth k B) : LayerDepth k (A+B) := by
  intro i j hij
  simp only [Matrix.add_apply,ha i j hij,hb i j hij,add_zero]
private theorem depth_mul {k l : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (ha : LayerDepth k A) (hb : LayerDepth l B) : LayerDepth (k+l) (A*B) := by
  classical
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t ht
  by_cases h : t.val < i.val+k
  · rw [ha i t h,zero_mul]
  · rw [hb t j (by omega),mul_zero]
private theorem depth_pow {k : ℕ} {A : Matrix (Fin n) (Fin n) F}
    (ha : LayerDepth k A) (d : ℕ) : LayerDepth (d*k) (A^d) := by
  induction d with
  | zero =>
    intro i j hij
    simp only [pow_zero,Matrix.one_apply]
    have hne : i ≠ j := by intro h; subst j; omega
    simp [hne]
  | succ d ih => simpa only [Nat.succ_mul,pow_succ] using depth_mul ih ha
private theorem depth_n_zero {A : Matrix (Fin n) (Fin n) F} (ha : LayerDepth n A) : A=0 := by
  ext i j
  exact ha i j (by omega)
private theorem depth_sum {T : Type} {k : ℕ} (s : Finset T)
    (f : T → Matrix (Fin n) (Fin n) F) (hf : ∀ t ∈ s, LayerDepth k (f t)) :
    LayerDepth k (∑ t ∈ s, f t) := by
  intro i j hij
  simp only [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro t ht
  exact hf t ht i j hij
private theorem inverse_unit_depth (g : Matrix.SpecialLinearGroup (Fin n) F)
    (hg : LayerDepth 1 (g.val-1)) : LayerDepth 1 ((g⁻¹).val-1) := by
  classical
  by_cases hn : n=0
  · subst n
    intro i
    exact Fin.elim0 i
  let A := g.val-1
  let S := ∑ t ∈ Finset.range n, (-A)^t
  have hA : LayerDepth 1 (-A) := depth_neg hg
  have hnil : (-A)^n=0 := depth_n_zero (by simpa using depth_pow hA n)
  have hS : S*g.val=1 := by
    have h := geom_sum_mul_neg (-A) n
    have he : 1-(-A)=g.val := by dsimp only [A]; abel
    rw [he,hnil,sub_zero] at h
    exact h
  have hgi : g.val*(g⁻¹).val=1 := by
    exact congrArg Subtype.val (mul_inv_cancel g)
  have hSinv : S=(g⁻¹).val := by
    calc
      S=S*(g.val*(g⁻¹).val) := by rw [hgi,mul_one]
      _ = (g⁻¹).val := by rw [← mul_assoc,hS,one_mul]
  rw [← hSinv]
  have hs : S=1+∑ t ∈ Finset.Ico 1 n, (-A)^t := by
    dsimp only [S]
    rw [← Finset.sum_range_add_sum_Ico _ (show 1 ≤ n by omega)]
    simp
  rw [hs,add_sub_cancel_left]
  apply depth_sum
  intro t ht
  exact depth_mono (depth_pow hA t) (by simpa using (Finset.mem_Ico.mp ht).1)
private theorem strip_depth (k : ℕ) (x : Fin n → F) : LayerDepth k (layerStrip k x) := by
  intro i j hij
  simp [layerStrip,show j.val ≠ i.val+k by omega]
private theorem strip_unit_det (k : ℕ) (hk : 0 < k) (x : Fin n → F) :
    Matrix.det (1+layerStrip k x)=1 := by
  classical
  have ht : Matrix.IsUpperTriangular (1+layerStrip k x) := by
    intro i j hij
    change j.val < i.val at hij
    have hne : i ≠ j := by intro h; subst j; omega
    simp [Matrix.add_apply,Matrix.one_apply,hne,layerStrip,show j.val ≠ i.val+k by omega]
  rw [Matrix.det_of_isUpperTriangular ht]
  apply Finset.prod_eq_one
  intro i hi
  simp [Matrix.add_apply,Matrix.one_apply,layerStrip,show k ≠ 0 by omega]

/-- Actual determinant-one strip witness in the genuine kth layer. -/
def stripUnit (k : ℕ) (hk : 0 < k) (x : Fin n → F) : Matrix.SpecialLinearGroup (Fin n) F :=
  ⟨1+layerStrip k x,strip_unit_det k hk x⟩
private theorem actual_group_layer_identity (k : ℕ) (hk : 0 < k)
    (x : Fin n → F) (g : Matrix.SpecialLinearGroup (Fin n) F)
    (hg : LayerDepth 1 (g.val-1)) :
    LayerDepth (k+1) (((stripUnit k hk x)⁻¹*g⁻¹*stripUnit k hk x*g).val-1) ∧
    ∀ (i : ℕ) (hi : i+k+1<n),
    (((stripUnit k hk x)⁻¹*g⁻¹*stripUnit k hk x*g).val-1) ⟨i,by omega⟩ ⟨i+k+1,hi⟩=
      (layerStrip k x*g.val-g.val*layerStrip k x) ⟨i,by omega⟩ ⟨i+k+1,hi⟩ := by
  let u := stripUnit k hk x
  let W := u.val*g.val-g.val*u.val
  have hW : LayerDepth (k+1) W := by
    have he : W=layerStrip k x*(g.val-1)-(g.val-1)*layerStrip k x := by
      dsimp only [W,u,stripUnit]
      noncomm_ring
    rw [he]
    have h2 : LayerDepth (k+1) ((g.val-1)*layerStrip k x) := by
      simpa only [Nat.add_comm] using depth_mul hg (strip_depth k x)
    have hs := depth_add (depth_mul (strip_depth k x) hg) (depth_neg h2)
    simpa only [sub_eq_add_neg] using hs
  have hu : LayerDepth 1 (u.val-1) := by
    change LayerDepth 1 ((1+layerStrip k x)-1)
    rw [add_sub_cancel_left]
    exact depth_mono (strip_depth k x) hk
  have hE : LayerDepth 1 ((u⁻¹).val*(g⁻¹).val-1) := by
    have hai := inverse_unit_depth u hu
    have hbi := inverse_unit_depth g hg
    have he : (u⁻¹).val*(g⁻¹).val-1=
        ((u⁻¹).val-1)*((g⁻¹).val-1)+((u⁻¹).val-1)+((g⁻¹).val-1) := by noncomm_ring
    rw [he]
    exact depth_add (depth_add (depth_mono (depth_mul hai hbi) (by omega)) hai) hbi
  have heq : (u⁻¹*g⁻¹*u*g).val-1=((u⁻¹).val*(g⁻¹).val-1)*W+W := by
    have h0 : (u⁻¹).val*(g⁻¹).val*(g.val*u.val)=1 := by
      exact congrArg Subtype.val (show u⁻¹*g⁻¹*(g*u)=1 by group)
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    dsimp only [W]
    noncomm_ring [h0]
  constructor
  · rw [heq]
    exact depth_add (depth_mono (depth_mul hE hW) (by omega)) hW
  · intro i hi
    have hEW : (((u⁻¹).val*(g⁻¹).val-1)*W) ⟨i,by omega⟩ ⟨i+k+1,hi⟩=0 :=
      depth_mul hE hW _ _ (by change i+k+1 < i+(1+(k+1)); omega)
    rw [heq,Matrix.add_apply,hEW,zero_add]
    have hWval : W=layerStrip k x*g.val-g.val*layerStrip k x := by
      dsimp only [W,u,stripUnit]
      noncomm_ring
    rw [hWval]
  
/-- Printed equation(13)'s ACTUAL group-commutator leading-layer
surjectivity in arbitrary matrix rank. The witness lies in the true kth
layer and is constructed, not assumed; the proper matrix is genuine SL.
This does not yet assert Proposition6.5 or a full unbounded-rank supplier. -/
theorem actual_proper_group_layer_surjective (k : ℕ) (hk : 0 < k)
    (g : Matrix.SpecialLinearGroup (Fin n) F) (hg : LayerDepth 1 (g.val-1))
    (hproper : ∀ i : ℕ, ∀ hi : i+1<n, g ⟨i,by omega⟩ ⟨i+1,hi⟩ ≠ 0)
    (target : Fin (n-(k+1)) → F) :
    ∃ u : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth k (u.val-1) ∧
      LayerDepth (k+1) ((u⁻¹*g⁻¹*u*g).val-1) ∧ ∀ i : Fin (n-(k+1)),
        ((u⁻¹*g⁻¹*u*g).val-1) ⟨i.val,by omega⟩ ⟨i.val+k+1,by omega⟩=target i := by
  obtain ⟨x,hx⟩ := actual_proper_layer_bracket_surjective k g.val hproper target
  refine ⟨stripUnit k hk x,?_,?_⟩
  · change LayerDepth k ((1+layerStrip k x)-1)
    rw [add_sub_cancel_left]
    exact strip_depth k x
  · refine ⟨(actual_group_layer_identity k hk x g hg).1,?_⟩
    intro i
    rw [(actual_group_layer_identity k hk x g hg).2]
    exact hx i
end NikolovSegal.PartIIUnitriangularLayers
