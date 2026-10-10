/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIPropositionSixSeven
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIProposition6_7
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIRadicalBoundaryPower
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIRadicalCenterProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
/-! Actual untwisted Proposition6.7, PartII pp262–263. Six genuine VALUE
batches retain the extra corner; no printed corner omission is assumed. -/
namespace NikolovSegal.PartIIProposition6_7
open PartIIUnitriangularLayers PartIIUnitriangularActions
open PartIIRadicalCoordinates PartIIRadicalMiddleProduct PartIIRadicalBoundaryPower PartIIRadicalCenterProduct
universe u
variable {F : Type u} [Field F] {k M : ℕ}
private def valueProduct {n : ℕ} (h : Fin M → Matrix.SpecialLinearGroup (Fin n) F)
    (a : Fin M → Fin n → Fˣ) (phi : Fin M → RingAut F) (eps : Fin M → Bool)
    (d : Fin M → ℕ) (x : Fin M → Matrix.SpecialLinearGroup (Fin n) F) :
    Matrix.SpecialLinearGroup (Fin n) F := NikolovSegal.orderedProduct (fun i =>
      (x i)⁻¹*((MulAut.conj (h i)*PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i))^(d i)) (x i))
private theorem residual_pair (P R : Matrix.SpecialLinearGroup (Fin (k+4)) F)
    (hP : InRadical P) (hR : InRadical R) :
    InRadical (P⁻¹*R) ∧ ∀ j : Fin (k+4), j≠first → j≠last →
      (P⁻¹*R) first j= -P first j+R first j ∧
      (P⁻¹*R) j.rev last= -P j.rev last+R j.rev last := by
  have hPi := actual_radical_inverse_mem P hP
  refine ⟨actual_radical_product_mem _ _ hPi hR,?_⟩
  intro j hj0 hjl
  have hjr0 : j.rev≠first := by
    intro h; have he := congrArg Fin.rev h; apply hjl; simpa [first,last] using he
  have hjrl : j.rev≠last := by
    intro h; have he := congrArg Fin.rev h; apply hj0; simpa [first,last] using he
  rw [(actual_radical_product_row_column P⁻¹ R hPi hR j hj0 hjl).1,
    (actual_radical_product_row_column P⁻¹ R hPi hR j.rev hjr0 hjrl).2,
    (actual_radical_inverse_row_column P hP j hj0 hjl).1,
    (actual_radical_inverse_row_column P hP j.rev hjr0 hjrl).2]
  exact ⟨rfl,rfl⟩
/-- Full actual radical VALUE reconstruction. All six diagonal INNER
correction tuples precede every nonlinear radical target. Original
positive divisor powers and the exact noncommutative product are kept. -/
theorem actual_six_batch_radical_product [Fintype F] [DecidableEq F]
    {q : ℕ} (hq : 0<q) (hM : (2*q)*(2*q+1)<M)
    (hF : (2*q+1)^(2*q)<Fintype.card F)
    (a0 a1 a2 a3 a4 a5 : Fin M → Fin (k+4) → Fˣ)
    (phi0 phi1 phi2 phi3 phi4 phi5 : Fin M → RingAut F)
    (eps0 eps1 eps2 eps3 eps4 eps5 : Fin M → Bool)
    (d0 d1 d2 d3 d4 d5 : Fin M → ℕ)
    (hd0 : ∀ i, 0<d0 i ∧ d0 i ∣ q) (hd1 : ∀ i, 0<d1 i ∧ d1 i ∣ q)
    (hd2 : ∀ i, 0<d2 i ∧ d2 i ∣ q) (hd3 : ∀ i, 0<d3 i ∧ d3 i ∣ q)
    (hd4 : ∀ i, 0<d4 i ∧ d4 i ∣ q) (hd5 : ∀ i, 0<d5 i ∧ d5 i ∣ q) :
    ∃ h0 h1 h2 h3 h4 h5 : Fin M → Matrix.SpecialLinearGroup (Fin (k+4)) F,
      (∀ i r c, r≠c → h0 i r c=0 ∧ h1 i r c=0 ∧ h2 i r c=0 ∧
        h3 i r c=0 ∧ h4 i r c=0 ∧ h5 i r c=0) ∧
      ∀ b : Matrix.SpecialLinearGroup (Fin (k+4)) F, InRadical b →
        ∃ x0 x1 x2 x3 x4 x5 : Fin M → Matrix.SpecialLinearGroup (Fin (k+4)) F,
          (∀ i, InRadical (x0 i) ∧ InRadical (x1 i) ∧ InRadical (x2 i) ∧
            InRadical (x3 i) ∧ InRadical (x4 i) ∧ InRadical (x5 i)) ∧
          valueProduct h0 a0 phi0 eps0 d0 x0*valueProduct h1 a1 phi1 eps1 d1 x1*
          valueProduct h2 a2 phi2 eps2 d2 x2*valueProduct h3 a3 phi3 eps3 d3 x3*
          valueProduct h4 a4 phi4 eps4 d4 x4*valueProduct h5 a5 phi5 eps5 d5 x5=b := by
  classical
  let J : Fin (k+4) := ⟨1,by omega⟩
  let K : Fin (k+4) := ⟨k+2,by omega⟩
  have hJ0 : J≠first := by intro h; have he := congrArg Fin.val h; change 1=0 at he; omega
  have hJl : J≠last := by intro h; have he := congrArg Fin.val h; change 1=k+3 at he; omega
  have hK0 : K≠first := by intro h; have he := congrArg Fin.val h; change k+2=0 at he; omega
  have hKl : K≠last := by intro h; have he := congrArg Fin.val h; change k+2=k+3 at he; omega
  have hJK : J≠K := by intro h; have he := congrArg Fin.val h; change 1=k+2 at he; omega
  obtain ⟨h0,hh0,c0⟩ := actual_inner_radical_middle_product (k:=k+1) hq hM hF a0 phi0 eps0 d0 hd0
  obtain ⟨h1,hh1,c1⟩ := actual_inner_radical_axis_product (l:=k+1) hq hM hF a1 phi1 eps1 d1 hd1 J hJ0 hJl false
  obtain ⟨h2,hh2,c2⟩ := actual_inner_radical_axis_product (l:=k+1) hq hM hF a2 phi2 eps2 d2 hd2 J hJ0 hJl true
  obtain ⟨h3,hh3,c3⟩ := actual_inner_radical_axis_product (l:=k+1) hq hM hF a3 phi3 eps3 d3 hd3 K hK0 hKl false
  obtain ⟨h4,hh4,c4⟩ := actual_inner_radical_axis_product (l:=k+1) hq hM hF a4 phi4 eps4 d4 hd4 K hK0 hKl true
  obtain ⟨h5,hh5,c5⟩ := actual_inner_radical_center_product (k:=k+1) hq hM hF a5 phi5 eps5 d5 hd5
  refine ⟨h0,h1,h2,h3,h4,h5,fun i r c hrc =>
    ⟨hh0 i r c hrc,hh1 i r c hrc,hh2 i r c hrc,hh3 i r c hrc,hh4 i r c hrc,hh5 i r c hrc⟩,?_⟩
  intro b hb
  obtain ⟨x0,hx0,hp0⟩ := c0 b hb
  let P0 := valueProduct h0 a0 phi0 eps0 d0 x0
  let R0 := P0⁻¹*b
  have hR0 := actual_middle_residual P0 b hp0.1 hb hp0.2
  obtain ⟨x1,hx1,hp1⟩ := c1 (R0 first J)
  let P1 := valueProduct h1 a1 phi1 eps1 d1 x1
  let R1 := P1⁻¹*R0
  have st1 := residual_pair P1 R0 hp1.1 hR0.1
  obtain ⟨x2,hx2,hp2⟩ := c2 (R1 J.rev last)
  let P2 := valueProduct h2 a2 phi2 eps2 d2 x2
  let R2 := P2⁻¹*R1
  have st2 := residual_pair P2 R1 hp2.1 st1.1
  obtain ⟨x3,hx3,hp3⟩ := c3 (R2 first K)
  let P3 := valueProduct h3 a3 phi3 eps3 d3 x3
  let R3 := P3⁻¹*R2
  have st3 := residual_pair P3 R2 hp3.1 st2.1
  obtain ⟨x4,hx4,hp4⟩ := c4 (R3 K.rev last)
  let P4 := valueProduct h4 a4 phi4 eps4 d4 x4
  let R4 := P4⁻¹*R3
  have st4 := residual_pair P4 R3 hp4.1 st3.1
  have hzero : ∀ j : Fin (k+4), j≠first → j≠last → R4 first j=0 ∧ R4 j.rev last=0 := by
    intro j hj0 hjl
    have s1 := st1.2 j hj0 hjl
    have s2 := st2.2 j hj0 hjl
    have s3 := st3.2 j hj0 hjl
    have s4 := st4.2 j hj0 hjl
    have p1 := hp1.2 j hj0 hjl
    have p2 := hp2.2 j hj0 hjl
    have p3 := hp3.2 j hj0 hjl
    have p4 := hp4.2 j hj0 hjl
    have r1 : R1 first j= -P1 first j+R0 first j := s1.1
    have r2 : R2 first j= -P2 first j+R1 first j := s2.1
    have r3 : R3 first j= -P3 first j+R2 first j := s3.1
    have r4 : R4 first j= -P4 first j+R3 first j := s4.1
    have z1 : R1 j.rev last= -P1 j.rev last+R0 j.rev last := s1.2
    have z2 : R2 j.rev last= -P2 j.rev last+R1 j.rev last := s2.2
    have z3 : R3 j.rev last= -P3 j.rev last+R2 j.rev last := s3.2
    have z4 : R4 j.rev last= -P4 j.rev last+R3 j.rev last := s4.2
    have pr1 : P1 first j=(if j=J then R0 first J else 0) := p1.1
    have pc1 : P1 j.rev last=0 := by simpa only [P1,valueProduct,Bool.false_eq_true,ite_true,ite_false,ite_self] using p1.2
    have pr2 : P2 first j=0 := by simpa only [P2,valueProduct,Bool.false_eq_true,ite_true,ite_false,ite_self] using p2.1
    have pc2 : P2 j.rev last=(if j=J then R1 J.rev last else 0) := p2.2
    have pr3 : P3 first j=(if j=K then R2 first K else 0) := p3.1
    have pc3 : P3 j.rev last=0 := by simpa only [P3,valueProduct,Bool.false_eq_true,ite_true,ite_false,ite_self] using p3.2
    have pr4 : P4 first j=0 := by simpa only [P4,valueProduct,Bool.false_eq_true,ite_true,ite_false,ite_self] using p4.1
    have pc4 : P4 j.rev last=(if j=K then R3 K.rev last else 0) := p4.2
    by_cases hJ : j=J
    · subst j
      simp only [ite_true,hJK,ite_false] at pr1 pc2 pr3 pc4
      constructor
      · simp only [r4,r3,r2,r1,pr1,pr2,pr3,pr4]; ring
      · simp only [z4,z3,z2,pc2,pc3,pc4]; ring
    · by_cases hK : j=K
      · subst j
        simp only [ite_true,Ne.symm hJK,ite_false] at pr1 pc2 pr3 pc4
        constructor
        · simp only [r4,r3,pr3,pr4]; ring
        · simp only [z4,pc4]; ring
      · have hjMid : Middle j := by
          have hn0 : j.val≠0 := by intro h; apply hj0; apply Fin.ext; exact h
          have hnl : j.val≠k+3 := by intro h; apply hjl; apply Fin.ext; exact h
          have hnJ : j.val≠1 := by intro h; apply hJ; apply Fin.ext; exact h
          have hnK : j.val≠k+2 := by intro h; apply hK; apply Fin.ext; exact h
          have hjn := j.isLt
          unfold Middle; omega
        have hm := hR0.2 j hjMid
        have hmr : R0 first j=0 := hm.1
        have hmc : R0 j.rev last=0 := hm.2
        simp only [hJ,hK,ite_false] at pr1 pc2 pr3 pc4
        constructor
        · simp only [r4,r3,r2,r1,pr1,pr2,pr3,pr4,hmr]; ring
        · simp only [z4,z3,z2,z1,pc1,pc2,pc3,pc4,hmc]; ring
  have htop : LayerDepth (k+3) (R4.val-1) := by
    apply actual_zero_noncorner_top R4 st4.1
    · intro j hj0 hjl; exact (hzero j hj0 hjl).1
    · intro j hj0 hjl
      have hjr0 : j.rev≠first := by
        intro h; have he := congrArg Fin.rev h; apply hjl; simpa [first,last] using he
      have hjrl : j.rev≠last := by
        intro h; have he := congrArg Fin.rev h; apply hj0; simpa [first,last] using he
      simpa only [Fin.rev_rev] using (hzero j.rev hjr0 hjrl).2
  obtain ⟨x5,hx5,hp5⟩ := c5 R4 htop
  refine ⟨x0,x1,x2,x3,x4,x5,fun i =>
    ⟨hx0 i,hx1 i,hx2 i,hx3 i,hx4 i,actual_top_layer_radical _ (hx5 i)⟩,?_⟩
  change P0*P1*P2*P3*P4*valueProduct h5 a5 phi5 eps5 d5 x5=b
  rw [show valueProduct h5 a5 phi5 eps5 d5 x5=R4 from hp5]
  dsimp only [R4,R3,R2,R1,R0]
  group
private abbrev Six (M : ℕ) := M+(M+(M+(M+(M+M))))
private def join6 {A : Type*} (a0 a1 a2 a3 a4 a5 : Fin M → A) : Fin (Six M) → A :=
  Fin.append a0 (Fin.append a1 (Fin.append a2 (Fin.append a3 (Fin.append a4 a5))))
private def i0 (j : Fin M) : Fin (Six M) := j.castAdd _
private def i1 (j : Fin M) : Fin (Six M) := (j.castAdd _).natAdd M
private def i2 (j : Fin M) : Fin (Six M) := ((j.castAdd _).natAdd M).natAdd M
private def i3 (j : Fin M) : Fin (Six M) := (((j.castAdd _).natAdd M).natAdd M).natAdd M
private def i4 (j : Fin M) : Fin (Six M) := ((((j.castAdd M).natAdd M).natAdd M).natAdd M).natAdd M
private def i5 (j : Fin M) : Fin (Six M) := ((((j.natAdd M).natAdd M).natAdd M).natAdd M).natAdd M
private theorem ordered_join6 {G : Type*} [Group G] (a0 a1 a2 a3 a4 a5 : Fin M → G) :
    NikolovSegal.orderedProduct (join6 a0 a1 a2 a3 a4 a5)=
      NikolovSegal.orderedProduct a0*NikolovSegal.orderedProduct a1*NikolovSegal.orderedProduct a2*
      NikolovSegal.orderedProduct a3*NikolovSegal.orderedProduct a4*NikolovSegal.orderedProduct a5 := by
  simp only [join6,NikolovSegal.orderedProduct,List.ofFn_fin_append,List.prod_append]
  group
private theorem join6_forall {A : Type*} (P : A → Prop) (a0 a1 a2 a3 a4 a5 : Fin M → A)
    (h0 : ∀ i, P (a0 i)) (h1 : ∀ i, P (a1 i)) (h2 : ∀ i, P (a2 i))
    (h3 : ∀ i, P (a3 i)) (h4 : ∀ i, P (a4 i)) (h5 : ∀ i, P (a5 i)) :
    ∀ i, P (join6 a0 a1 a2 a3 a4 a5 i) := by
  simpa only [join6,Fin.forall_fin_add,Fin.append_left,Fin.append_right] using
    And.intro h0 (And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 h5))))
/-- Quantitative actual untwisted Proposition6.7, with a rigorously
proved chosen length 6*(2q(2q+1)+1), including the full corner. N,C are
chosen before ALL finite fields, ranks and prescribed tuples. Every
correction is an actual diagonal SL INNER correction, before ALL targets. -/
theorem actual_proposition6_7_uniform_inner_V_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ k : ℕ,
      ∀ (a : Fin N → Fin (k+4) → Fˣ) (phi : Fin N → RingAut F)
        (eps : Fin N → Bool) (d : Fin N → ℕ), (∀ i, 0<d i ∧ d i ∣ q) →
      ∃ h : Fin N → Matrix.SpecialLinearGroup (Fin (k+4)) F,
        (∀ i r c, r≠c → h i r c=0) ∧
        ∀ b : Matrix.SpecialLinearGroup (Fin (k+4)) F, InRadical b →
          ∃ x : Fin N → Matrix.SpecialLinearGroup (Fin (k+4)) F,
            (∀ i, InRadical (x i)) ∧
            NikolovSegal.orderedProduct (fun i => (x i)⁻¹*
              ((MulAut.conj (h i)*PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i))^(d i)) (x i))=b := by
  let M := (2*q)*(2*q+1)+1
  refine ⟨Six M,(2*q+1)^(2*q),by dsimp only [Six,M]; omega,?_⟩
  intro F _ _ _ hF k a phi eps d hd
  obtain ⟨h0,h1,h2,h3,h4,h5,hh,hcover⟩ := actual_six_batch_radical_product (k:=k) (M:=M)
    hq (by dsimp only [M]; omega) hF
    (fun j => a (i0 j)) (fun j => a (i1 j)) (fun j => a (i2 j))
    (fun j => a (i3 j)) (fun j => a (i4 j)) (fun j => a (i5 j))
    (fun j => phi (i0 j)) (fun j => phi (i1 j)) (fun j => phi (i2 j))
    (fun j => phi (i3 j)) (fun j => phi (i4 j)) (fun j => phi (i5 j))
    (fun j => eps (i0 j)) (fun j => eps (i1 j)) (fun j => eps (i2 j))
    (fun j => eps (i3 j)) (fun j => eps (i4 j)) (fun j => eps (i5 j))
    (fun j => d (i0 j)) (fun j => d (i1 j)) (fun j => d (i2 j))
    (fun j => d (i3 j)) (fun j => d (i4 j)) (fun j => d (i5 j))
    (fun j => hd _) (fun j => hd _) (fun j => hd _) (fun j => hd _) (fun j => hd _) (fun j => hd _)
  let h := join6 h0 h1 h2 h3 h4 h5
  have hhdiag : ∀ i r c, r≠c → h i r c=0 := by
    apply join6_forall (fun g : Matrix.SpecialLinearGroup (Fin (k+4)) F => ∀ r c, r≠c → g r c=0)
    · exact fun j r c hrc => (hh j r c hrc).1
    · exact fun j r c hrc => (hh j r c hrc).2.1
    · exact fun j r c hrc => (hh j r c hrc).2.2.1
    · exact fun j r c hrc => (hh j r c hrc).2.2.2.1
    · exact fun j r c hrc => (hh j r c hrc).2.2.2.2.1
    · exact fun j r c hrc => (hh j r c hrc).2.2.2.2.2
  refine ⟨h,hhdiag,?_⟩
  intro b hb
  obtain ⟨x0,x1,x2,x3,x4,x5,hx,he⟩ := hcover b hb
  let x := join6 x0 x1 x2 x3 x4 x5
  have hxV : ∀ i, InRadical (x i) := join6_forall InRadical x0 x1 x2 x3 x4 x5
    (fun j => (hx j).1) (fun j => (hx j).2.1) (fun j => (hx j).2.2.1)
    (fun j => (hx j).2.2.2.1) (fun j => (hx j).2.2.2.2.1) (fun j => (hx j).2.2.2.2.2)
  let v0 := fun j => (x0 j)⁻¹*((MulAut.conj (h0 j)*PartIIProposition6_5.diagonalFieldGraph (a (i0 j)) (phi (i0 j)) (eps (i0 j)))^(d (i0 j))) (x0 j)
  let v1 := fun j => (x1 j)⁻¹*((MulAut.conj (h1 j)*PartIIProposition6_5.diagonalFieldGraph (a (i1 j)) (phi (i1 j)) (eps (i1 j)))^(d (i1 j))) (x1 j)
  let v2 := fun j => (x2 j)⁻¹*((MulAut.conj (h2 j)*PartIIProposition6_5.diagonalFieldGraph (a (i2 j)) (phi (i2 j)) (eps (i2 j)))^(d (i2 j))) (x2 j)
  let v3 := fun j => (x3 j)⁻¹*((MulAut.conj (h3 j)*PartIIProposition6_5.diagonalFieldGraph (a (i3 j)) (phi (i3 j)) (eps (i3 j)))^(d (i3 j))) (x3 j)
  let v4 := fun j => (x4 j)⁻¹*((MulAut.conj (h4 j)*PartIIProposition6_5.diagonalFieldGraph (a (i4 j)) (phi (i4 j)) (eps (i4 j)))^(d (i4 j))) (x4 j)
  let v5 := fun j => (x5 j)⁻¹*((MulAut.conj (h5 j)*PartIIProposition6_5.diagonalFieldGraph (a (i5 j)) (phi (i5 j)) (eps (i5 j)))^(d (i5 j))) (x5 j)
  have hv : (fun i => (x i)⁻¹*((MulAut.conj (h i)*PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i))^(d i)) (x i))=
      join6 v0 v1 v2 v3 v4 v5 := by
    funext i
    simp only [x,h,join6,v0,v1,v2,v3,v4,v5]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left,i0]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.append_right,Fin.append_left,i1]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp only [Fin.append_right,Fin.append_left,i2]
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
          · simp only [Fin.append_right,Fin.append_left,i3]
          · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
            · simp only [Fin.append_right,Fin.append_left,i4]
            · simp only [Fin.append_right,i5]
  refine ⟨x,hxV,?_⟩
  rw [hv,ordered_join6]
  exact he
end NikolovSegal.PartIIProposition6_7
