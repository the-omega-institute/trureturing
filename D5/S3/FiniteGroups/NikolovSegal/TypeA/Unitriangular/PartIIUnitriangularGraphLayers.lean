/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphLayers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularLayersGlobal
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace NikolovSegal.PartIIUnitriangularGraphLayers
/-- Printed p265 symmetric alternating torus, as integral diagonal weights.
For odd matrix size, opposite sides of the central unit have inverse
weights; for even size the alternating zero and minus-one pattern works modulo scalars. -/
def mirrorWeight (n i : ℕ) : ℤ :=
  if n%2=0 then -(i%2:ℤ)
  else if i≤n/2 then ((n/2-i)%2:ℤ) else -((i-n/2)%2:ℤ)
private theorem odd_weight_difference (n i j : ℕ) (hi : i<n) (hj : j<n)
    (hij : i<j) (hodd : (j-i)%2=1) :
    mirrorWeight n i-mirrorWeight n j=1 ∨ mirrorWeight n i-mirrorWeight n j= -1 := by
  unfold mirrorWeight
  split_ifs <;> omega
private theorem reflected_weight (n i : ℕ) (hi : i<n) :
    mirrorWeight n (n-(i+1))=(if n%2=0 then -1 else 0)-mirrorWeight n i := by
  unfold mirrorWeight
  split_ifs <;> omega
/-- The two quantitative torus facts are derived for ACTUAL matrix
indices, including central-crossing roots. No sign/commutation law input. -/
theorem actual_mirror_odd_root_weights {n : ℕ} (i j : Fin n)
    (hij : i.val<j.val) (hodd : (j.val-i.val)%2=1) :
    (mirrorWeight n i.val-mirrorWeight n j.val=1 ∨ mirrorWeight n i.val-mirrorWeight n j.val= -1) ∧
    mirrorWeight n j.rev.val-mirrorWeight n i.rev.val=mirrorWeight n i.val-mirrorWeight n j.val := by
  refine ⟨odd_weight_difference n i.val j.val i.isLt j.isLt hij hodd,?_⟩
  change mirrorWeight n (n-(j.val+1))-mirrorWeight n (n-(i.val+1))=_
  rw [reflected_weight n j.val j.isLt,reflected_weight n i.val i.isLt]
  ring


open PartIIUnitriangularLayers PartIIUnitriangularActions PartIIFieldMaps
universe u
variable {F : Type u} [Field F] {n : ℕ}

/-- The genuine p265 reflection-invariant torus on arbitrary-rank SL. -/
def mirrorTorus (lambda : Fˣ) : MulAut (Matrix.SpecialLinearGroup (Fin n) F) :=
  (unitOdd% diagonalAut) (fun i => lambda ^ mirrorWeight n i.val)
private def rootWeight (lambda : Fˣ) (k : ℕ) (i : Fin (n-k)) : Fˣ :=
  lambda ^ (mirrorWeight n i.val-mirrorWeight n (i.val+k))
private theorem mirror_coordinate (lambda : Fˣ) (k : ℕ)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (i : Fin (n-k)) :
    (unitOdd% coordinate) k (mirrorTorus lambda a) i=
      (rootWeight lambda k i:F)*(unitOdd% coordinate) k a i := by
  change ((unitOdd% diagonalAut) (fun j : Fin n => lambda ^ mirrorWeight n j.val) a)
    ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩=_
  rw [(unitOdd% diagonal_entry)]
  have he : lambda ^ mirrorWeight n i.val*(lambda ^ mirrorWeight n (i.val+k))⁻¹=rootWeight lambda k i := by
    exact (zpow_sub lambda _ _).symm
  change _=(rootWeight lambda k i:F)*a ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩
  calc
    _ = ((lambda ^ mirrorWeight n i.val:Fˣ):F)*(((lambda ^ mirrorWeight n (i.val+k))⁻¹:Fˣ):F)*a ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩ := by ring
    _ = _ := by rw [← Units.val_mul,he]
private theorem mirror_depth (lambda : Fˣ) (k : ℕ)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1)) :
    LayerDepth k ((mirrorTorus lambda a).val-1) :=
  (unitOdd% diagonal_depth) _ k a ha
private theorem raw_graph_depth (k : ℕ) (hk : 0<k)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1)) :
    LayerDepth k (((unitAction% rawGraph) a).val-1) := by
  have hi := (unitOdd% inverse_depth) k hk a ha
  intro i j hij
  have hrev : i.rev.val < j.rev.val+k := by simp only [Fin.val_rev]; omega
  have h := hi j.rev i.rev hrev
  simp only [Matrix.sub_apply] at h ⊢
  rw [(unitAction% rawGraph_entry)]
  convert h using 1
  simp [Matrix.one_apply,Fin.rev_inj,eq_comm]
private theorem raw_graph_coordinate (k : ℕ) (hk : 0<k)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1))
    (i : Fin (n-k)) :
    (unitOdd% coordinate) k ((unitAction% rawGraph) a) i=
      -(unitOdd% coordinate) k a i.rev := by
  change ((unitAction% rawGraph) a) ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩=_
  rw [(unitAction% rawGraph_entry)]
  have h1 : (⟨i.val+k,by omega⟩ : Fin n).rev=⟨i.rev.val,by omega⟩ := by
    apply Fin.ext; simp only [Fin.val_rev]; omega
  have h2 : (⟨i.val,by omega⟩ : Fin n).rev=⟨i.rev.val+k,by omega⟩ := by
    apply Fin.ext; simp only [Fin.val_rev]; omega
  rw [h1,h2]
  exact (unitOdd% inverse_coordinate) k hk a ha i.rev
private theorem height_coordinate (lambda : Fˣ) (k : ℕ)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (i : Fin (n-k)) :
    (unitOdd% coordinate) k (heightTorus lambda a) i=
      (lambda:F)^k*(unitOdd% coordinate) k a i := by
  change (heightTorus lambda a) ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩=_
  rw [(unitAction% torus_entry),pow_add]
  have he : (((lambda⁻¹:Fˣ):F)^i.val)*(lambda:F)^i.val=1 := by rw [← mul_pow]; simp
  calc
    _ = (((lambda⁻¹:Fˣ):F)^i.val*(lambda:F)^i.val)*((lambda:F)^k*a ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩) := by ring
    _ = _ := by rw [he,one_mul]; rfl
private theorem graph_depth (k : ℕ) (hk : 0<k)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1)) :
    LayerDepth k ((positiveGraph a).val-1) :=
  (unitAction% torus_depth) (-1:Fˣ) k _ (raw_graph_depth k hk a ha)
private theorem graph_odd_coordinate (k : ℕ) (hk : 0<k) (hodd : k%2=1)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1))
    (i : Fin (n-k)) :
    (unitOdd% coordinate) k (positiveGraph a) i=(unitOdd% coordinate) k a i.rev := by
  change (unitOdd% coordinate) k (heightTorus (-1:Fˣ) ((unitAction% rawGraph) a)) i=_
  rw [height_coordinate,raw_graph_coordinate k hk a ha]
  have hneg : (-1:F)^k= -1 := by
    have hp : Odd k := Nat.odd_iff.mpr hodd
    exact hp.neg_one_pow
  simpa only [Units.val_neg,Units.val_one,hneg,neg_one_mul,neg_neg]
private theorem field_graph_depth (phi : RingAut F) (eps : Bool) (k : ℕ) (hk : 0<k)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1)) :
    LayerDepth k ((fieldGraphAut phi eps a).val-1) := by
  cases eps
  · exact (unitOdd% field_depth) phi k a ha
  · exact (unitOdd% field_depth) phi k _ (graph_depth k hk a ha)
private theorem field_graph_odd_coordinate (phi : RingAut F) (eps : Bool)
    (k : ℕ) (hk : 0<k) (hodd : k%2=1)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1))
    (i : Fin (n-k)) :
    (unitOdd% coordinate) k (fieldGraphAut phi eps a) i=
      phi ((unitOdd% coordinate) k a (if eps then i.rev else i)) := by
  cases eps
  · exact (unitOdd% field_coordinate) phi k a i
  · change (unitOdd% coordinate) k (fieldAut phi (positiveGraph a)) i=_
    rw [(unitOdd% field_coordinate),graph_odd_coordinate k hk hodd a ha]
    rfl
private theorem rootWeight_reverse (lambda : Fˣ) (k : ℕ) (hk : 0<k) (hodd : k%2=1)
    (i : Fin (n-k)) : rootWeight lambda k i.rev=rootWeight lambda k i := by
  have h := (actual_mirror_odd_root_weights (⟨i.val,by omega⟩ : Fin n)
    ⟨i.val+k,by omega⟩ (by change i.val < i.val+k; omega) (by simpa using hodd)).2
  have he : mirrorWeight n i.rev.val-mirrorWeight n (i.rev.val+k)=mirrorWeight n i.val-mirrorWeight n (i.val+k) := by
    simp only [Fin.val_rev] at h ⊢
    have h1 : n-k-(i.val+1)=n-(i.val+k+1) := by omega
    have h2 : n-k-(i.val+1)+k=n-(i.val+1) := by omega
    rw [h1]
    have h3 : n-(i.val+k+1)+k=n-(i.val+1) := by omega
    rw [h3]; exact h
  unfold rootWeight
  rw [he]
private theorem mirror_graph_depth (lambda : Fˣ) (phi : RingAut F) (eps : Bool)
    (k : ℕ) (hk : 0<k) (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (d : ℕ) :
    LayerDepth k ((((mirrorTorus lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) a).val-1) := by
  induction d with
  | zero => simpa only [pow_zero,MulAut.one_apply] using ha
  | succ d ih =>
    rw [pow_succ',MulAut.mul_apply,MulAut.mul_apply]
    exact mirror_depth lambda k _ (field_graph_depth phi eps k hk _ ih)
private theorem mirror_graph_step (lambda : Fˣ) (phi : RingAut F) (eps : Bool)
    (k : ℕ) (hk : 0<k) (hodd : k%2=1)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1))
    (i : Fin (n-k)) :
    (unitOdd% coordinate) k ((mirrorTorus lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F)) a) i=
      (rootWeight lambda k i:F)*phi ((unitOdd% coordinate) k a (if eps then i.rev else i)) := by
  rw [MulAut.mul_apply,mirror_coordinate,field_graph_odd_coordinate phi eps k hk hodd a ha]
private theorem mirror_graph_double (lambda : Fˣ) (phi : RingAut F) (eps : Bool)
    (k : ℕ) (hk : 0<k) (hodd : k%2=1)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1))
    (i : Fin (n-k)) :
    (unitOdd% coordinate) k (((mirrorTorus lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^2) a) i=
      (rootWeight lambda k i:F)*phi (rootWeight lambda k i:F)*(phi^2) ((unitOdd% coordinate) k a i) := by
  have hb : LayerDepth k ((((mirrorTorus lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F)) a).val-1)) :=
    mirror_depth lambda k _ (field_graph_depth phi eps k hk a ha)
  rw [pow_two,MulAut.mul_apply,mirror_graph_step lambda phi eps k hk hodd
    ((mirrorTorus lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F)) a) hb,
    mirror_graph_step lambda phi eps k hk hodd a ha]
  cases eps <;> simp only [Bool.false_eq_true,ite_false,ite_true,Fin.rev_rev,
    rootWeight_reverse lambda k hk hodd,map_mul,pow_two,RingAut.mul_apply] <;> ring

/-- Actual doubled-power odd-root transport for arbitrary prescribed
field/positive-graph actions. Reflection-invariant torus weights and the
component formula are proved, not assumed. This is the p265--266 scalar
bridge; it does not assume scalar or matrix PRODUCT coverage. -/
theorem actual_mirror_field_graph_doubled_power (lambda : Fˣ) (phi : RingAut F)
    (eps : Bool) (k : ℕ) (hk : 0<k) (hodd : k%2=1)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1)) (d : ℕ) :
    LayerDepth k ((((mirrorTorus lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(2*d)) a).val-1) ∧
    ∀ i : Fin (n-k), (unitOdd% coordinate) k
      (((mirrorTorus lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(2*d)) a) i=
      orbitProduct phi (2*d) (rootWeight lambda k i:F)*(phi^(2*d)) ((unitOdd% coordinate) k a i) := by
  refine ⟨mirror_graph_depth lambda phi eps k hk a ha _,?_⟩
  induction d with
  | zero => intro i; simp [orbitProduct]
  | succ d ih =>
    intro i
    rw [show 2*(d+1)=2+2*d by omega,pow_add,MulAut.mul_apply,
      mirror_graph_double lambda phi eps k hk hodd _ (mirror_graph_depth lambda phi eps k hk a ha _) i,
      ih i,map_mul]
    have hN : orbitProduct phi (2+2*d) (rootWeight lambda k i:F)=
        (rootWeight lambda k i:F)*phi (rootWeight lambda k i:F)*
        phi (phi (orbitProduct phi (2*d) (rootWeight lambda k i:F))) := by
      rw [show 2+2*d=(2*d+1)+1 by omega,(rootFieldKernel% orbitProduct_succ),
        (rootFieldKernel% orbitProduct_succ),map_mul]
      ring
    rw [hN]
    simp only [pow_two,pow_add,RingAut.mul_apply]
    ring
end NikolovSegal.PartIIUnitriangularGraphLayers
