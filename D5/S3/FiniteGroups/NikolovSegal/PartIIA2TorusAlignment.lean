/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIA2TorusAlignment
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIA2TorusAlignment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIA2RootNormalization
import D5.S3.FiniteGroups.NikolovSegal.PartIISL3UnipotentNormalizer
import D5.S3.FiniteGroups.NikolovSegal.PartIISL3UnipotentSylow
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace NikolovSegal.PartIIA2TorusAlignment
open PartIIA2Orbital
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

private theorem upper_diagonal_nonzero (g : SL(3,F))
    (ht : ∀ i j : Fin 3, j < i → g i j=0) (i : Fin 3) : g i i ≠ 0 := by
  have hd := g.property
  rw [Matrix.det_fin_three] at hd
  have h10 := ht 1 0 (by decide)
  have h20 := ht 2 0 (by decide)
  have h21 := ht 2 1 (by decide)
  simp only [h10,h20,h21,mul_zero,zero_mul,add_zero,sub_zero] at hd
  intro hi
  fin_cases i <;> simp_all

private theorem upper_diagonal_mul (g h : SL(3,F))
    (hg : ∀ i j : Fin 3, j < i → g i j=0)
    (hh : ∀ i j : Fin 3, j < i → h i j=0) (i : Fin 3) :
    (g*h) i i=g i i*h i i := by
  fin_cases i
  all_goals simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_succ,
    hg 1 0 (by decide),hg 2 0 (by decide),hg 2 1 (by decide),
    hh 1 0 (by decide),hh 2 0 (by decide),hh 2 1 (by decide)]

/-- Simultaneous ACTUAL triangular matrix alignment by one unipotent matrix.
The only arithmetic hypothesis is that the finite subgroup order is invertible
in the field. The aligned subgroup may have arbitrary nontrivial off-diagonal
entries; the conjugator is constructed by a weighted group average. -/
theorem upper_finite_subgroup_diagonal_alignment (K : Subgroup SL(3,F)) [Fintype K]
    (ht : ∀ k : K, ∀ i j : Fin 3, j < i → (k:SL(3,F)) i j=0)
    (hcard : (Fintype.card K:F) ≠ 0) :
    ∃ u : SL(3,F), u ∈ upperUnipotent ∧ ∀ k : K,
      (u⁻¹*(k:SL(3,F))*u).val = Matrix.diagonal (fun i => (k:SL(3,F)) i i) := by
  classical
  let A := fun k : K => (k:SL(3,F)).val
  let N := fun k : K => A k*Matrix.diagonal (fun i => (A k i i)⁻¹)
  let P : Matrix (Fin 3) (Fin 3) F := (Fintype.card K:F)⁻¹ • ∑ k : K,N k
  have hn : ∀ k i, A k i i ≠ 0 := by intro k i; exact upper_diagonal_nonzero _ (ht k) i
  have hpd : ∀ i, P i i=1 := by
    intro i
    change (Fintype.card K:F)⁻¹*((∑ k : K,N k) i i)=1
    have he : (∑ k : K,N k) i i = ∑ k : K,N k i i := by
      exact Matrix.sum_apply i i Finset.univ N
    rw [he]
    simp [N,Matrix.mul_diagonal,hn,hcard]
  have hpt : ∀ i j, j < i → P i j=0 := by
    intro i j hij
    change (Fintype.card K:F)⁻¹*((∑ k : K,N k) i j)=0
    have he : (∑ k : K,N k) i j = ∑ k : K,N k i j := by
      exact Matrix.sum_apply i j Finset.univ N
    rw [he]
    simp [N,A,Matrix.mul_diagonal,ht _ i j hij]
  let u := upper3 (P 0 1) (P 1 2) (P 0 2)
  have hup : u.val=P := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u,upper3,hpd,hpt 1 0 (by decide),hpt 2 0 (by decide),hpt 2 1 (by decide)]
  have hN : ∀ h k : K, A h*N k=N (h*k)*Matrix.diagonal (fun i => A h i i) := by
    intro h k
    have hdiag : ∀ i, A (h*k) i i=A h i i*A k i i :=
      fun i => upper_diagonal_mul _ _ (ht h) (ht k) i
    have hAk : A (h*k)=A h*A k := rfl
    ext i j
    simp only [N,hAk,← Matrix.mul_assoc,Matrix.mul_diagonal]
    rw [← hAk,hdiag]
    field_simp [hn]
  have hP : ∀ h : K, A h*P=P*Matrix.diagonal (fun i => A h i i) := by
    intro h
    calc
      A h*P = (Fintype.card K:F)⁻¹ • ∑ k : K,A h*N k := by
        simp [P,Finset.mul_sum,Matrix.mul_smul]
      _ = (Fintype.card K:F)⁻¹ • ∑ k : K,N (h*k)*Matrix.diagonal (fun i => A h i i) := by
        simp_rw [hN]
      _ = (Fintype.card K:F)⁻¹ • ((∑ k : K,N (h*k))*Matrix.diagonal (fun i => A h i i)) := by
        rw [Finset.sum_mul]
      _ = P*Matrix.diagonal (fun i => A h i i) := by
        have he : (∑ k : K,N (h*k)) = ∑ k : K,N k := by
          exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun k => rfl)
        rw [he]
        simp [P,Matrix.smul_mul]
  refine ⟨u,⟨P 0 1,P 1 2,P 0 2,rfl⟩,?_⟩
  intro k
  change (u⁻¹).val*(k:SL(3,F)).val*u.val=Matrix.diagonal (fun i => (k:SL(3,F)) i i)
  rw [Matrix.mul_assoc,hup,hP]
  rw [← hup,← Matrix.mul_assoc,← Matrix.SpecialLinearGroup.coe_mul,inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one,one_mul]
/-- The literal determinant-one diagonal torus, parameterized by two units. -/
def diagonalPair : Fˣ × Fˣ →* SL(3,F) where
  toFun x := ⟨Matrix.diagonal (![↑x.1,↑x.2,↑(x.1*x.2)⁻¹] : Fin 3 → F),by
    simp only [Matrix.det_diagonal,Fin.prod_univ_succ,Matrix.cons_val_zero,
      Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one]
    simpa only [← Units.val_mul,mul_assoc,Units.val_one] using
      congrArg (fun z : Fˣ => (z:F)) (mul_inv_cancel (x.1*x.2))⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply,Matrix.one_apply]
  map_mul' x y := by
    apply Subtype.ext
    change Matrix.diagonal (![↑(x*y).1,↑(x*y).2,↑((x*y).1*(x*y).2)⁻¹] : Fin 3 → F)=
      Matrix.diagonal (![↑x.1,↑x.2,↑(x.1*x.2)⁻¹] : Fin 3 → F)*
        Matrix.diagonal (![↑y.1,↑y.2,↑(y.1*y.2)⁻¹] : Fin 3 → F)
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    fin_cases i <;> simp [Units.val_mul,mul_inv_rev,mul_comm,mul_left_comm,mul_assoc]

private theorem diagonalPair_injective : Function.Injective (diagonalPair (F := F)) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have h0 := congrArg (fun g : SL(3,F) => g 0 0) h
  have h1 := congrArg (fun g : SL(3,F) => g 1 1) h
  apply Prod.ext
  · exact Units.ext h0
  · exact Units.ext h1

def diagonalTorus : Subgroup SL(3,F) := (diagonalPair (F := F)).range

private theorem card_diagonalTorus [Fintype F] [DecidableEq F] :
    Nat.card (diagonalTorus (F := F))=(Fintype.card F-1)^2 := by
  change Nat.card ((diagonalPair (F := F)).range)=(Fintype.card F-1)^2
  rw [← Nat.card_congr (MonoidHom.ofInjective (diagonalPair_injective (F := F))).toEquiv,
    Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_units]
  ring

/-- ACTUAL bare-automorphism diagonal torus image alignment. The order
invertibility is proved from its actual two-unit parameterization; no
coprimality, decomposition or conjugacy oracle. The input triangularity is
exactly the geometric Borel-normalization obligation supplied separately. -/
theorem actual_torus_image_unipotent_alignment [Fintype F] [DecidableEq F]
    (beta : MulAut SL(3,F))
    (ht : ∀ x : Fˣ × Fˣ, ∀ i j : Fin 3, j < i → beta (diagonalPair x) i j=0) :
    ∃ u : SL(3,F), u ∈ upperUnipotent ∧ ∀ x : Fˣ × Fˣ,
      (u⁻¹*beta (diagonalPair x)*u).val=
        Matrix.diagonal (fun i => beta (diagonalPair x) i i) := by
  classical
  let K := (diagonalTorus (F := F)).map beta.toMonoidHom
  letI : Fintype K := Fintype.ofFinite _
  have hK : ∀ k : K, ∀ i j : Fin 3, j < i → (k:SL(3,F)) i j=0 := by
    intro k i j hij
    obtain ⟨g,⟨x,rfl⟩,hg⟩ := k.prop
    change (k:SL(3,F)) i j=0
    rw [← hg]
    exact ht x i j hij
  have hc : Fintype.card K=(Fintype.card F-1)^2 := by
    rw [← Nat.card_eq_fintype_card,← Nat.card_congr
      ((diagonalTorus (F := F)).equivMapOfInjective beta.toMonoidHom beta.injective).toEquiv]
    exact card_diagonalTorus
  have hfcard : ((Fintype.card F-1:ℕ):F)= -1 := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr (Fintype.card_pos (α := F))),
      FiniteField.cast_card_eq_zero,Nat.cast_one,zero_sub]
  have hcard : (Fintype.card K:F) ≠ 0 := by
    rw [hc,Nat.cast_pow,hfcard]
    exact pow_ne_zero 2 (neg_ne_zero.mpr one_ne_zero)
  obtain ⟨u,hu,hdiag⟩ := upper_finite_subgroup_diagonal_alignment K hK hcard
  refine ⟨u,hu,?_⟩
  intro x
  exact hdiag ⟨beta (diagonalPair x),Subgroup.mem_map_of_mem beta.toMonoidHom ⟨x,rfl⟩⟩
private theorem mem_torus_of_diagonal (g : SL(3,F)) (d : Fin 3 → F)
    (hd : g.val=Matrix.diagonal d) : g ∈ diagonalTorus := by
  have he := g.property
  rw [hd,Matrix.det_diagonal] at he
  have hp : (d 0*d 1)*d 2=1 := by
    simpa [Fin.prod_univ_succ,mul_assoc] using he
  have hn0 : d 0 ≠ 0 := by intro h; simp [h] at hp
  have hn1 : d 1 ≠ 0 := by intro h; simp [h] at hp
  have h2 : (d 0*d 1)⁻¹=d 2 := by
    apply mul_left_cancel₀ (mul_ne_zero hn0 hn1)
    rw [mul_inv_cancel₀ (mul_ne_zero hn0 hn1)]
    exact hp.symm
  refine ⟨(Units.mk0 (d 0) hn0,Units.mk0 (d 1) hn1),?_⟩
  apply Subtype.ext
  change Matrix.diagonal (![d 0,d 1,↑((Units.mk0 (d 0) hn0)*(Units.mk0 (d 1) hn1))⁻¹] : Fin 3 → F)=g.val
  rw [hd]
  apply congrArg Matrix.diagonal
  funext i
  fin_cases i
  · rfl
  · rfl
  · simpa [Units.val_inv_eq_inv_val,Units.val_mul] using h2

private theorem normalize_inner_image (U : Subgroup SL(3,F))
    (beta : MulAut SL(3,F)) (g : SL(3,F))
    (h : U.map beta.toMonoidHom=U.map (MulAut.conj g).toMonoidHom) :
    U.map (MulAut.conj g⁻¹*beta).toMonoidHom=U := by
  have he := congrArg (fun H : Subgroup SL(3,F) => H.map (MulAut.conj g⁻¹).toMonoidHom) h
  rw [Subgroup.map_map,Subgroup.map_map] at he
  have hi : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom=MonoidHom.id _ := by
    ext z
    simp [MulAut.conj_apply,mul_assoc]
  rw [hi,Subgroup.map_id] at he
  exact he

/-- Actual arbitrary-bare-SL3 normalization of BOTH the unipotent subgroup
and its diagonal torus. Sylow supplies the first conjugator, the concrete
Borel theorem supplies triangularity of the torus image, and the weighted
matrix average supplies the second. No root image, flag, semilinearity,
conjugacy or coverage hypothesis remains. This is geometric normalization;
root alignment and full scalar PRODUCT are separate remaining obligations. -/
theorem actual_bare_SL3_U_torus_normalization [Fintype F] [DecidableEq F]
    (beta : MulAut SL(3,F)) :
    ∃ g : SL(3,F),
      upperUnipotent.map (MulAut.conj g⁻¹*beta).toMonoidHom=upperUnipotent ∧
      diagonalTorus.map (MulAut.conj g⁻¹*beta).toMonoidHom=diagonalTorus := by
  classical
  letI : Fact (Nat.Prime (ringChar F)) := ⟨CharP.char_is_prime F (ringChar F)⟩
  obtain ⟨g,hg⟩ := PartIISL3UnipotentSylow.automorphism_U3_conjugate (ringChar F) beta
  let alpha := MulAut.conj g⁻¹*beta
  have hU : upperUnipotent.map alpha.toMonoidHom=upperUnipotent :=
    normalize_inner_image _ beta g hg
  have htri : ∀ x : Fˣ × Fˣ, ∀ i j : Fin 3, j < i → alpha (diagonalPair x) i j=0 := by
    intro x
    apply (PartIISL3UnipotentNormalizer.automorphism_upper_iff alpha hU _).mpr
    intro i j hij
    change Matrix.diagonal (![↑x.1,↑x.2,↑(x.1*x.2)⁻¹] : Fin 3 → F) i j=0
    exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)
  obtain ⟨u,hu,htu⟩ := actual_torus_image_unipotent_alignment alpha htri
  let alpha1 := MulAut.conj u⁻¹*alpha
  have huNorm : u⁻¹ ∈ Subgroup.normalizer (upperUnipotent (F := F) : Set SL(3,F)) :=
    Subgroup.le_normalizer (upperUnipotent.inv_mem hu)
  have huU : upperUnipotent.map (MulAut.conj u⁻¹).toMonoidHom=upperUnipotent :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp huNorm
  have hU1 : upperUnipotent.map alpha1.toMonoidHom=upperUnipotent := by
    change upperUnipotent.map ((MulAut.conj u⁻¹).toMonoidHom.comp alpha.toMonoidHom)=upperUnipotent
    rw [← Subgroup.map_map,hU,huU]
  have hTle : diagonalTorus.map alpha1.toMonoidHom ≤ diagonalTorus := by
    rintro z ⟨h,⟨x,rfl⟩,rfl⟩
    apply mem_torus_of_diagonal _ (fun i => alpha (diagonalPair x) i i)
    simpa [alpha1,MulAut.mul_apply,MulAut.conj_apply,mul_assoc] using htu x
  have hT : diagonalTorus.map alpha1.toMonoidHom=diagonalTorus := by
    apply Subgroup.eq_of_le_of_card_ge hTle
    exact (Nat.card_congr (diagonalTorus.equivMapOfInjective alpha1.toMonoidHom alpha1.injective).toEquiv).le
  have halpha : MulAut.conj (g*u)⁻¹*beta=alpha1 := by
    ext z
    simp [alpha1,alpha,MulAut.mul_apply,MulAut.conj_apply,mul_inv_rev,mul_assoc]
  exact ⟨g*u,by rw [halpha]; exact hU1,by rw [halpha]; exact hT⟩
end NikolovSegal.PartIIA2TorusAlignment
