/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIPropositionSixFive
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIProposition6_5
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularGraphFixedLayers
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace NikolovSegal.PartIIProposition6_5
open PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitriangularGraphLayers PartIIUnitriangularFieldSupply
universe u
variable {F : Type u} [Field F] {n M : ℕ}
/-- Actual prescribed diagonal/field/positive-graph automorphism of SL. -/
def diagonalFieldGraph (a : Fin n → Fˣ) (phi : RingAut F) (eps : Bool) :
    MulAut (Matrix.SpecialLinearGroup (Fin n) F) :=
  (unitOdd% diagonalAut) a*fieldGraphAut phi eps
private def join {A : Type*} (a b c d : Fin M → A) (e : A) :
    Fin (M+(M+(M+(M+1)))) → A :=
  Fin.append a (Fin.append b (Fin.append c (Fin.append d (fun _ : Fin 1 => e))))
private def i1 (j : Fin M) : Fin (M+(M+(M+(M+1)))) := j.castAdd _
private def i2 (j : Fin M) : Fin (M+(M+(M+(M+1)))) := (j.castAdd _).natAdd M
private def iP (j : Fin M) : Fin (M+(M+(M+(M+1)))) := ((j.castAdd _).natAdd M).natAdd M
private def iN (j : Fin M) : Fin (M+(M+(M+(M+1)))) := (((j.castAdd 1).natAdd M).natAdd M).natAdd M
private def i0 : Fin (M+(M+(M+(M+1)))) := (((((0:Fin 1).natAdd M).natAdd M).natAdd M).natAdd M)
private theorem ordered_join {G : Type*} [Group G] (a b c d : Fin M → G) (e : G) :
    NikolovSegal.orderedProduct (join a b c d e)=
      NikolovSegal.orderedProduct a*NikolovSegal.orderedProduct b*
      NikolovSegal.orderedProduct c*NikolovSegal.orderedProduct d*e := by
  simp only [join,NikolovSegal.orderedProduct,List.ofFn_fin_append,List.prod_append]
  simp only [List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one]
  group
private theorem diagonal_cancel (a b : Fin n → Fˣ) (phi : RingAut F) (eps : Bool) :
    (unitOdd% diagonalAut) (fun i => b i*(a i)⁻¹)*diagonalFieldGraph a phi eps=
      (unitOdd% diagonalAut) b*fieldGraphAut phi eps := by
  have he : (unitOdd% diagonalAut) (fun i => b i*(a i)⁻¹)*(unitOdd% diagonalAut) a=(unitOdd% diagonalAut) b := by
    apply MulEquiv.ext; intro g
    apply Matrix.SpecialLinearGroup.ext; intro i j
    rw [MulAut.mul_apply,(unitOdd% diagonal_entry),(unitOdd% diagonal_entry),(unitOdd% diagonal_entry)]
    simp only [Units.val_mul,mul_inv_rev,inv_inv,Units.val_inv_eq_inv_val]
    have hi : (a i:F) ≠ 0 := (a i).ne_zero
    have hj : (a j:F) ≠ 0 := (a j).ne_zero
    field_simp
    <;> ring
  unfold diagonalFieldGraph
  rw [← mul_assoc,he]
private theorem height_diagonal (lambda : Fˣ) :
    (unitOdd% diagonalAut) (fun i : Fin n => lambda⁻¹^i.val)=heightTorus lambda := by
  apply MulEquiv.ext; intro g
  apply Matrix.SpecialLinearGroup.ext; intro i j
  rw [(unitOdd% diagonal_entry),(unitAction% torus_entry)]
  simp only [inv_pow,inv_inv,Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val]
private theorem actual_prescribed_diagonal_U_product [Fintype F] [DecidableEq F]
    {q : ℕ} (hq : 0<q) (hM : (2*q)*(2*q+1)<M)
    (hF : (2*q+1)^(2*q)<Fintype.card F)
    (a : Fin (M+(M+(M+(M+1)))) → Fin n → Fˣ)
    (phi : Fin (M+(M+(M+(M+1)))) → RingAut F)
    (eps : Fin (M+(M+(M+(M+1)))) → Bool)
    (d : Fin (M+(M+(M+(M+1)))) → ℕ)
    (hd : ∀ i, 0<d i ∧ d i ∣ q) :
    ∃ eta : Fin (M+(M+(M+(M+1)))) → Fin n → Fˣ,
    ∃ u : Fin (M+(M+(M+(M+1)))) → Matrix.SpecialLinearGroup (Fin n) F,
      (∀ i, LayerDepth 1 ((u i).val-1)) ∧
      ∀ b : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth 1 (b.val-1) →
        ∃ x : Fin (M+(M+(M+(M+1)))) → Matrix.SpecialLinearGroup (Fin n) F,
          (∀ i, LayerDepth 1 ((x i).val-1)) ∧
          NikolovSegal.orderedProduct (fun i => (x i)⁻¹*
            ((MulAut.conj (u i)*(unitOdd% diagonalAut) (eta i)*diagonalFieldGraph (a i) (phi i) (eps i) :
              MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d i)) (x i))=b := by
  classical
  obtain ⟨l1,l2,lp,lm,l0,u0,hu0,hcover⟩ :=
    PartIIUnitriangularGraphFixedLayers.actual_uniform_field_graph_U_product (n:=n) hq hM hF
      (fun j => phi (i1 j)) (fun j => phi (i2 j)) (fun j => phi (iP j)) (fun j => phi (iN j))
      (fun j => eps (i1 j)) (fun j => eps (i2 j)) (fun j => eps (iP j)) (fun j => eps (iN j))
      (fun j => d (i1 j)) (fun j => d (i2 j)) (fun j => d (iP j)) (fun j => d (iN j))
      (fun j => hd _) (fun j => hd _) (fun j => hd _) (fun j => hd _)
      (phi (i0 (M:=M))) (eps (i0 (M:=M))) (d (i0 (M:=M))) (hd _)
  let desired : Fin (M+(M+(M+(M+1)))) → Fin n → Fˣ := join
    (fun j i => (l1 j)⁻¹^i.val) (fun j i => (l2 j)⁻¹^(i.val/2))
    (fun j i => lp j ^ mirrorWeight n i.val) (fun j i => (lm j)⁻¹ ^ mirrorWeight n i.val)
    (fun i => l0⁻¹^i.val)
  let eta := fun j i => desired j i*(a j i)⁻¹
  let u : Fin (M+(M+(M+(M+1)))) → Matrix.SpecialLinearGroup (Fin n) F :=
    join (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) u0
  have hu : ∀ i, LayerDepth 1 ((u i).val-1) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [u,join,LayerDepth]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [u,join,LayerDepth]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp [u,join,LayerDepth]
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
          · simp [u,join,LayerDepth]
          · simpa [u,join] using hu0
  refine ⟨eta,u,hu,?_⟩
  intro b hb
  obtain ⟨x1,x2,xp,xm,y,hx,hy,he⟩ := hcover b hb
  let x := join x1 x2 xp xm y
  have hxx : ∀ i, LayerDepth 1 ((x i).val-1) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [x,join] using (hx j).1
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa [x,join] using (hx j).2.1
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simpa [x,join] using (hx j).2.2.1
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
          · simpa [x,join] using (hx j).2.2.2
          · simpa [x,join] using hy
  let v1 := fun j => (x1 j)⁻¹*((layerTorus 1 (l1 j)*fieldGraphAut (phi (i1 j)) (eps (i1 j)) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d (i1 j))) (x1 j)
  let v2 := fun j => (x2 j)⁻¹*((layerTorus 2 (l2 j)*fieldGraphAut (phi (i2 j)) (eps (i2 j)) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d (i2 j))) (x2 j)
  let vp := fun j => (xp j)⁻¹*((mirrorTorus (lp j)*fieldGraphAut (phi (iP j)) (eps (iP j)) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d (iP j))) (xp j)
  let vm := fun j => (xm j)⁻¹*((mirrorTorus ((lm j)⁻¹)*fieldGraphAut (phi (iN j)) (eps (iN j)) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d (iN j))) (xm j)
  let beta0 : MulAut (Matrix.SpecialLinearGroup (Fin n) F) := MulAut.conj u0*(heightTorus l0*fieldGraphAut (phi (i0 (M:=M))) (eps (i0 (M:=M))))
  let v0 := y⁻¹*(beta0^(d (i0 (M:=M)))) y
  have hv : (fun i => (x i)⁻¹*((MulAut.conj (u i)*(unitOdd% diagonalAut) (eta i)*diagonalFieldGraph (a i) (phi i) (eps i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d i)) (x i))=join v1 v2 vp vm v0 := by
    have hc : ∀ i, MulAut.conj (u i)*(unitOdd% diagonalAut) (eta i)*diagonalFieldGraph (a i) (phi i) (eps i)=
        MulAut.conj (u i)*((unitOdd% diagonalAut) (desired i)*fieldGraphAut (phi i) (eps i)) := by
      intro i
      dsimp only [eta]
      rw [mul_assoc,diagonal_cancel]
    funext i
    rw [hc i]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [u,desired,x,join,Fin.append_left]
      simp only [map_one,one_mul,v1,layerTorus,Nat.div_one]
      rfl
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [u,desired,x,join,Fin.append_left,Fin.append_right]
        simp only [map_one,one_mul,v2,layerTorus]
        rfl
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp only [u,desired,x,join,Fin.append_left,Fin.append_right]
          simp only [map_one,one_mul,vp,mirrorTorus]
          rfl
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
          · simp only [u,desired,x,join,Fin.append_left,Fin.append_right]
            simp only [map_one,one_mul,vm,mirrorTorus]
            rfl
          · have hj : j=0 := Subsingleton.elim _ _
            subst j
            simp only [u,desired,x,join,Fin.append_right]
            rw [height_diagonal]
            rfl
  refine ⟨x,hxx,?_⟩
  rw [hv,ordered_join]
  exact he

/-- Quantitative actual Proposition6.5 for every rank and prescribed
DIAGONAL/field/positive-graph tuple. Length/cutoff are fixed before fields,
ranks and all tuples. Actual diagonal corrections and unitriangular u are
chosen before ALL nonlinear targets. Diagonal corrections are allowed
by Proposition6.5; this does NOT assert they are inner SL automorphisms
and does NOT close the uniform finite-simple scalar supplier. -/
theorem actual_proposition6_5_uniform_diagonal_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ n : ℕ,
      ∀ (a : Fin N → Fin n → Fˣ) (phi : Fin N → RingAut F) (eps : Fin N → Bool)
        (d : Fin N → ℕ), (∀ i, 0<d i ∧ d i ∣ q) →
      ∃ eta : Fin N → Fin n → Fˣ, ∃ u : Fin N → Matrix.SpecialLinearGroup (Fin n) F,
        (∀ i, LayerDepth 1 ((u i).val-1)) ∧
        ∀ b : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth 1 (b.val-1) →
          ∃ x : Fin N → Matrix.SpecialLinearGroup (Fin n) F,
            (∀ i, LayerDepth 1 ((x i).val-1)) ∧
            NikolovSegal.orderedProduct (fun i => (x i)⁻¹*
              ((MulAut.conj (u i)*(unitOdd% diagonalAut) (eta i)*diagonalFieldGraph (a i) (phi i) (eps i) :
                MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d i)) (x i))=b := by
  let M := (2*q)*(2*q+1)+1
  refine ⟨M+(M+(M+(M+1))),(2*q+1)^(2*q),by dsimp only [M]; omega,?_⟩
  intro F _ _ _ hF n a phi eps d hd
  exact actual_prescribed_diagonal_U_product hq (by dsimp only [M]; omega) hF a phi eps d hd
end NikolovSegal.PartIIProposition6_5
