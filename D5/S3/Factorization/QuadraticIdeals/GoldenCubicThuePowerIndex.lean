/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicThuePowerIndex
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicThuePowerIndex
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The signed native Thue index form and exact monogenic order index. -/

import D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueMaximalOrder
import Mathlib.Data.Int.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Charpoly.Basic

set_option autoImplicit false
open scoped NumberField Polynomial
open Algebra Polynomial Matrix Module
open D5.S1.Scale
open D5.S3.Factorization.QuadraticIdeals
open EisensteinOddQuotient GoldenCubicThueDescent GoldenCubicThueEisenstein
open GoldenCubicThueMaximalOrder CubicIntegralLattice

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicThuePowerIndex

theorem card_quotient_span_of_det_ne_zero {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] (b : Module.Basis ι ℤ M) (v : ι → M)
    (hn : (b.toMatrix v).det ≠ 0) :
    Nat.card (M ⧸ Submodule.span ℤ (Set.range v)) = (b.toMatrix v).det.natAbs := by
  let Q := Submodule.span ℤ (Set.range v)
  have hl : LinearIndependent ℤ v := by
    apply LinearIndependent.of_comp b.equivFun.toLinearMap
    have hk := Matrix.linearIndependent_cols_of_det_ne_zero hn
    convert hk using 1
    ext j i
    simp [Matrix.col, Module.Basis.toMatrix_apply, Module.Basis.equivFun_apply]
  let : Module.Free ℤ M := Module.Free.of_basis b
  let : Module.Finite ℤ M := Module.Finite.of_basis b
  let bQ : Module.Basis ι ℤ Q := Module.Basis.span hl
  have h := Submodule.natAbs_det_basis_change b Q bQ
  have he : ((↑) ∘ bQ : ι → M) = v := by
    funext i
    exact congrArg Subtype.val (Module.Basis.span_apply hl i)
  rw [he, Module.Basis.det_apply] at h
  exact h.symm

theorem discr_eq_det_sq_mul_field_discr
    {L : Type*} [Field L] [NumberField L] {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ (𝓞 L)) (v : ι → 𝓞 L) :
    Algebra.discr ℚ (fun i => (v i : L)) =
      ((b.toMatrix v).det : ℚ)^2 * (NumberField.discr L : ℚ) := by
  let B : ι → L := fun i => (b i : L)
  let M := (b.toMatrix v).map (Int.castRingHom ℚ)
  have h : B ᵥ* M.map (algebraMap ℚ L) = fun i => (v i : L) := by
    funext j
    have hj := congrArg (fun z : 𝓞 L => (z : L)) (b.sum_toMatrix_smul_self (v := v) (j := j))
    simpa [B, M, Matrix.vecMul, dotProduct, mul_comm, Algebra.smul_def] using hj
  have hM : M.det = ((b.toMatrix v).det : ℚ) :=
    ((Int.castRingHom ℚ).map_det (b.toMatrix v)).symm
  rw [← h, Algebra.discr_of_matrix_vecMul, hM]
  exact congrArg (((b.toMatrix v).det : ℚ)^2 * ·)
    (discr_eq_of_integralBasis b)

theorem card_quotient_span_of_cubic_discr
    {L : Type*} [Field L] [NumberField L]
    (b : Basis (Fin 3) ℤ (𝓞 L)) (v : Fin 3 → 𝓞 L)
    (P : ℕ) (hP : 0 < P)
    (hv : Algebra.discr ℚ (fun i => (v i : L)) = 324 * (P : ℚ)^4)
    (hL : (NumberField.discr L : ℚ) = 81 * (P : ℚ)^2) :
    Nat.card (𝓞 L ⧸ Submodule.span ℤ (Set.range v)) = 2*P := by
  let d := (b.toMatrix v).det
  have hpq : (0 : ℚ) < P := by exact_mod_cast hP
  have h := discr_eq_det_sq_mul_field_discr b v
  change _ = (d : ℚ)^2 * _ at h
  rw [hv,hL] at h
  have hsq : (d : ℚ)^2 = (2*(P : ℚ))^2 := by
    apply mul_right_cancel₀ (show 81*(P : ℚ)^2 ≠ 0 by positivity)
    rw [← h]
    ring
  have hd : d ≠ 0 := by
    intro hz
    rw [hz] at hsq
    norm_num at hsq
    nlinarith [mul_pos hpq hpq]
  have ha : d.natAbs = (2 * (P : ℤ)).natAbs := Int.natAbs_eq_iff_sq_eq.mpr (by exact_mod_cast hsq)
  rw [card_quotient_span_of_det_ne_zero b v hd]
  change d.natAbs = _
  rw [ha, Int.natAbs_mul]
  simp

/-- The marked native binary cubic is the signed coordinate determinant of a
power triple, not the norm of its generating element. -/
theorem native_power_index_det {R L : Type*} [CommRing R] [CommRing L] [Algebra R L]
    (b : Module.Basis (Fin 3) R L) (A B C u v : R) (α β : L)
    (hb0 : b 0 = 1) (hb1 : b 1 = α) (hb2 : b 2 = β)
    (ha : α^2 = A • β - B • α)
    (hab : α*β = (-C) • α - algebraMap R L (A^2))
    (hbb : β^2 = (-C) • β - A • α - algebraMap R L (B*A)) :
    let τ := u • α + v • β
    (b.toMatrix (![1,τ,τ^2] : Fin 3 → L)).det =
      A*u^3+B*u^2*v+C*u*v^2+A*v^3 := by
  let τ := u • α + v • β
  let c := -2*u*v*A^2-v^2*B*A
  let a := -B*u^2-2*C*u*v-A*v^2
  let d := A*u^2-C*v^2
  have ht : τ^2 = c • b 0 + a • b 1 + d • b 2 := by
    dsimp only [τ,c,a,d]
    rw [hb0,hb1,hb2]
    simp only [Algebra.smul_def, map_sub, map_mul, map_neg, map_pow, map_ofNat,
      mul_one] at *
    linear_combination
      (algebraMap R L u)^2*ha + 2*(algebraMap R L u)*(algebraMap R L v)*hab +
      (algebraMap R L v)^2*hbb
  have hM : b.toMatrix (![1,τ,τ^2] : Fin 3 → L) = !![1,0,c;0,u,a;0,v,d] := by
    ext i j
    fin_cases j
    · change (b.repr 1) i = _
      rw [← hb0]
      fin_cases i <;> simp [Module.Basis.repr_self]
    · change (b.repr τ) i = _
      have ht' : τ = u • b 1 + v • b 2 := by rw [hb1,hb2]
      rw [ht']
      fin_cases i <;> simp [Module.Basis.repr_self]
    · change (b.repr (τ^2)) i = _
      rw [ht]
      fin_cases i <;> simp [Module.Basis.repr_self]
  change (b.toMatrix (![1,τ,τ^2] : Fin 3 → L)).det = _
  rw [hM, Matrix.det_fin_three]
  simp [a,d]
  ring

/-- In an actual cubic number field, the additive group of the monogenic
order is exactly the integer span of its three initial powers. -/
theorem integer_adjoin_eq_cubic_span {L : Type*} [Field L] [NumberField L]
    (b : Module.Basis (Fin 3) ℤ (𝓞 L)) (τ : 𝓞 L) :
    (adjoin ℤ ({τ} : Set (𝓞 L))).toSubmodule =
      Submodule.span ℤ (Set.range (![1,τ,τ^2] : Fin 3 → (𝓞 L))) := by
  let W := Submodule.span ℤ (Set.range (![1,τ,τ^2] : Fin 3 → (𝓞 L)))
  let _ : Module.Free ℤ (𝓞 L) := Module.Free.of_basis b
  let _ : Module.Finite ℤ (𝓞 L) := Module.Finite.of_basis b
  let T := Algebra.lmul ℤ (𝓞 L) τ
  let f := T.charpoly
  have h3deg : f.natDegree = 3 := by
    dsimp [f]
    rw [LinearMap.charpoly_natDegree, Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hfc : f.coeff 3 = 1 := by
    rw [← h3deg]
    exact (LinearMap.charpoly_monic T).coeff_natDegree
  have h3 : τ^3 = ((-(f.coeff 2):ℤ):𝓞 L)*τ^2+
        ((-(f.coeff 1):ℤ):𝓞 L)*τ+((-(f.coeff 0):ℤ):𝓞 L) := by
    have h0 := Algebra.aeval_self_charpoly_lmul (R:=ℤ) τ
    change Polynomial.aeval τ f = 0 at h0
    have hr := f.as_sum_range_C_mul_X_pow
    rw [h3deg] at hr
    have hh := congrArg (Polynomial.aeval τ) hr
    rw [h0] at hh
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      zero_add, map_add, map_mul, map_pow, Polynomial.aeval_X, map_intCast,
      eq_intCast, hfc, Int.cast_one, one_mul, pow_zero, pow_one, mul_one] at hh
    push_cast
    linear_combination -hh
  have h1 : 1 ∈ W := Submodule.subset_span ⟨0,rfl⟩
  have hτ : τ ∈ W := Submodule.subset_span ⟨1,rfl⟩
  have hτ2 : τ^2 ∈ W := Submodule.subset_span ⟨2,rfl⟩
  apply le_antisymm
  · exact adjoin_le_of_monic_cubic τ _ _ _ h3 W h1 hτ hτ2
  · rw [Submodule.span_le]
    rintro w ⟨i,rfl⟩
    have hm : τ ∈ adjoin ℤ ({τ} : Set (𝓞 L)) := self_mem_adjoin_singleton _ _
    fin_cases i
    · exact (adjoin ℤ ({τ} : Set (𝓞 L))).one_mem
    · exact hm
    · exact (adjoin ℤ ({τ} : Set (𝓞 L))).pow_mem hm 2

/-- The signed Thue value -2 multiplies the old table discriminant by
exactly four. The selected generator itself is integral. -/
theorem native_tau_discr_and_integral {L : Type*} [Field L] [NumberField L]
    (A D P u v : ℤ) (x : L)
    (hn : A^2-A*D+D^2=P^2)
    (hx : (A:L)*x^3-3*(D:L)*x^2+3*((D:L)-(A:L))*x+(A:L)=0)
    (hval : A*u^3-3*D*u^2*v+3*(D-A)*u*v^2+A*v^3 = -2)
    (b : Module.Basis (Fin 3) ℚ L)
    (hb0 : b 0=1) (hb1 : b 1=(A:L)*x) (hb2 : b 2=(A:L)*x^2-3*(D:L)*x) :
    let α := (A:L)*x
    let β := (A:L)*x^2-3*(D:L)*x
    let τ := (u:L)*α+(v:L)*β
    IsIntegral ℤ τ ∧ Algebra.discr ℚ (![1,τ,τ^2] : Fin 3 → L) = 324*(P:ℚ)^4 := by
  let α := (A:L)*x
  let β := (A:L)*x^2-3*(D:L)*x
  let τ := (u:L)*α+(v:L)*β
  let B : ℤ := -3*D
  let C : ℤ := 3*(D-A)
  have hBC : (A:L)*x^3+(B:L)*x^2+(C:L)*x+(A:L)=0 := by
    dsimp [B,C]
    push_cast
    linear_combination hx
  have hβ' : (A:L)*x^2+(B:L)*x = β := by dsimp [B,β]; push_cast; ring
  have hint := scaled_basis_integral (L:=L) A B C x hBC
  rw [hβ'] at hint
  have hintu (n : ℤ) : IsIntegral ℤ (n:L) := by
    simpa only [eq_intCast] using (isIntegral_algebraMap (A:=L) (x:=n))
  have hτ : IsIntegral ℤ τ := ((hintu u).mul hint.1).add ((hintu v).mul hint.2)
  refine ⟨hτ,?_⟩
  have htable := scaled_basis_products (A:L) (B:L) (C:L) x hBC
  dsimp only at htable
  rw [hβ'] at htable
  have haa : α^2 = (A:ℚ) • β - (B:ℚ) • α := by
    simpa only [Algebra.smul_def, map_intCast] using htable.1
  have hab : α*β = (-(C:ℚ)) • α - algebraMap ℚ L ((A:ℚ)^2) := by
    simpa only [Algebra.smul_def, map_intCast, map_neg, map_pow] using htable.2.1
  have hbb : β^2 = (-(C:ℚ)) • β - (A:ℚ) • α - algebraMap ℚ L ((B:ℚ)*(A:ℚ)) := by
    simpa only [Algebra.smul_def, map_intCast, map_neg, map_mul] using htable.2.2
  have hdet := native_power_index_det b (A:ℚ) (B:ℚ) (C:ℚ) (u:ℚ) (v:ℚ) α β
    hb0 hb1 hb2 haa hab hbb
  have hTau : (u:ℚ) • α + (v:ℚ) • β = τ := by
    simp only [τ,Algebra.smul_def,map_intCast]
  dsimp only at hdet
  rw [hTau] at hdet
  have hvalQ : (A:ℚ)*(u:ℚ)^3+(B:ℚ)*(u:ℚ)^2*(v:ℚ)+(C:ℚ)*(u:ℚ)*(v:ℚ)^2+
      (A:ℚ)*(v:ℚ)^3 = -2 := by
    have hh : A*u^3+B*u^2*v+C*u*v^2+A*v^3 = -2 := by
      dsimp [B,C]
      linear_combination hval
    exact_mod_cast hh
  rw [hvalQ] at hdet
  have hnQ : (A:ℚ)^2-(A:ℚ)*(D:ℚ)+(D:ℚ)^2=(P:ℚ)^2 := by exact_mod_cast hn
  have hcQ : (C:ℚ)=3*((D:ℚ)-(A:ℚ)) := by dsimp [C]; push_cast; ring
  have hbQ : (B:ℚ)=(-3)*(D:ℚ) := by dsimp [B]; push_cast; ring
  rw [hcQ] at hab hbb
  rw [hbQ] at haa hbb
  have ht := traceMatrix_det_scaled_native b (A:ℚ) (D:ℚ) (P:ℚ) α β hb0 hb1 hb2
    (by simpa only [pow_two] using haa) hab (by simpa only [pow_two] using hbb) hnQ
  change Algebra.discr ℚ (![1,τ,τ^2] : Fin 3 → L) = _
  rw [← b.toMatrix_map_vecMul (![1,τ,τ^2] : Fin 3 → L), Algebra.discr_of_matrix_vecMul, hdet,
      Algebra.discr_def, ht]
  ring

local instance splittingFieldNumberField (f : ℚ[X]) : NumberField f.SplittingField :=
  NumberField.of_module_finite ℚ f.SplittingField

set_option maxHeartbeats 1200000 in
/-- The given oriented factorization selects an integral generator whose
monogenic order has exact additive index 2P in the full ring of integers. -/
theorem actual_factorization_power_index
    (j P Q : ℕ) (hj : 1 ≤ j) (hP : P.Prime) (hQ : Q.Prime) (hPQ : P ≠ Q)
    (hfact : blockNorm ((goldenLucas (3^j)-1).toNat) = P^2 * Q^3) :
    ∃ pi gamma : EisensteinOrder,
      Ideal.span {pi} = orientedIdeal ((goldenLucas (3^j)-1).toNat) ⊔
        Ideal.span {(P:EisensteinOrder)} ∧
      Ideal.span {gamma} = orientedIdeal ((goldenLucas (3^j)-1).toNat) ⊔
        Ideal.span {(Q:EisensteinOrder)} ∧
      QuadraticAlgebra.norm pi = (P:ℤ) ∧ QuadraticAlgebra.norm gamma = (Q:ℤ) ∧
      orientedFactor ((goldenLucas (3^j)-1).toNat) = pi^2*gamma^3 ∧
      let A := pi.re^2-pi.im^2
      let D := 2*pi.re*pi.im-pi.im^2
      let f := (⟨(A:ℚ),(-3*D:ℤ),(3*(D-A):ℤ),(A:ℚ)⟩ : Cubic ℚ).toPoly
      let L := f.SplittingField
      NumberField.discr L = 81*(P:ℤ)^2 ∧
      ∃ (x : L) (τ : 𝓞 L),
        IntermediateField.adjoin ℚ ({x} : Set L)=⊤ ∧
        (A:L)*x^3-3*(D:L)*x^2+3*((D:L)-(A:L))*x+(A:L)=0 ∧
        (τ:L) = (gamma.re:L)*((A:L)*x)+(gamma.im:L)*((A:L)*x^2-3*(D:L)*x) ∧
        Nat.card ((𝓞 L) ⧸ (adjoin ℤ ({τ} : Set (𝓞 L))).toSubmodule) = 2*P := by
  classical
  obtain ⟨pi,gamma,hi,hnorm,_,hig,hnormg,_,hprod,hv,hp,hPA,hPE,h3A,h3E,h3P,
    hn,_,hdim,x,b,hx,hgen,hb0,hb1,hb2⟩ := actual_factorization_marked_thue_pair j P Q hj hP hQ hPQ hfact
  let A := pi.re^2-pi.im^2
  let D := 2*pi.re*pi.im-pi.im^2
  let f := (⟨(A:ℚ),(-3*D:ℤ),(3*(D-A):ℤ),(A:ℚ)⟩ : Cubic ℚ).toPoly
  let L := f.SplittingField
  let α := (A:L)*x
  let β := (A:L)*x^2-3*(D:L)*x
  let τ := (gamma.re:L)*α+(gamma.im:L)*β
  obtain ⟨hτ,hdiscr⟩ := native_tau_discr_and_integral A D (P:ℤ) gamma.re gamma.im x
    hn hx hv b hb0 hb1 hb2
  have dfield := (native_field_discriminant A D (P:ℤ) x hp hPA hPE h3A h3E h3P hn hx
    hgen b hb0 hb1 hb2).1
  let t : 𝓞 L := ⟨τ,hτ⟩
  let v : Fin 3 → (𝓞 L) := ![1,t,t^2]
  let bInt := NumberField.RingOfIntegers.basis L
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 L)) = 3 := by
    rw [← Module.finrank_eq_card_basis (NumberField.integralBasis L)]
    exact hdim
  let B := bInt.reindex (Fintype.equivFinOfCardEq hcard)
  have hco : (fun i => (v i : L)) = (![1,τ,τ^2] : Fin 3 → L) := by
    funext i
    fin_cases i <;> rfl
  have hvd : Algebra.discr ℚ (fun i => (v i : L)) = 324*(P:ℚ)^4 := by
    rw [hco]
    change Algebra.discr ℚ (![1,τ,τ^2] : Fin 3 → L) = _
    simpa only [Int.cast_natCast] using hdiscr
  have hLd : (NumberField.discr L : ℚ) = 81*(P:ℚ)^2 := by
    have hc := congrArg (fun z : ℤ => (z:ℚ)) dfield
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_natCast] using hc
  have hh := card_quotient_span_of_cubic_discr B v P hP.pos hvd hLd
  have hidx : Nat.card ((𝓞 L) ⧸ (adjoin ℤ ({t} : Set (𝓞 L))).toSubmodule) = 2*P := by
    rw [integer_adjoin_eq_cubic_span B t]
    exact hh
  exact ⟨pi,gamma,hi,hig,hnorm,hnormg,hprod,dfield,x,t,hgen,hx,rfl,hidx⟩

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicThuePowerIndex
