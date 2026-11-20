/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueMaximalOrder
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicThueMaximalOrder
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The maximal integral lattice and signed field discriminant of the native Thue cubic. -/

import D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice
import D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueEisenstein
import D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueRootChange

open Algebra Polynomial D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice
open D5.S3.Factorization.QuadraticIdeals
open scoped Polynomial
set_option autoImplicit false
namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueMaximalOrder

/-- The original four integral generators span the whole integral closure.
Here the primitive norm, unit readouts, and the cubic rational basis are
explicit. The original square-role ideal supplies them. -/
theorem native_maximal_span {L : Type*} [Field L] [NumberField L]
    (A D P : ℤ) (x : L) (hp : Prime P)
    (hPA : ¬ P ∣ A) (hPE : ¬ P ∣ A-2*D)
    (h3A : (3:ℤ) ∣ A-1) (h3E : ¬ (3:ℤ) ∣ A-2*D) (h3P : (3:ℤ) ∣ P-1)
    (hn : A^2-A*D+D^2=P^2)
    (hx : (A:L)*x^3-3*(D:L)*x^2+3*((D:L)-(A:L))*x+(A:L)=0)
    (hxgen : IntermediateField.adjoin ℚ ({x} : Set L) = ⊤)
    (b : Module.Basis (Fin 3) ℚ L) (hb0 : b 0 = 1)
    (hb1 : b 1 = (A:L)*x) (hb2 : b 2 = (A:L)*x^2-3*(D:L)*x) :
    let α := (A:L)*x
    let β := (A:L)*x^2-3*(D:L)*x
    let θ := (α-(D:L))^2/(P:L)
    Submodule.span ℤ (Set.range (![1,α,β,θ] : Fin 4 → L)) = (integralClosure ℤ L).toSubmodule := by
  let α := (A:L)*x
  let β := (A:L)*x^2-3*(D:L)*x
  let θ := (α-(D:L))^2/(P:L)
  let E : ℤ := A-2*D
  let B : ℤ := -3*D
  let C : ℤ := 3*(D-A)
  let M := Submodule.span ℤ (Set.range (![1,α,β,θ] : Fin 4 → L))
  change M = (integralClosure ℤ L).toSubmodule
  have hmod3 : Prime (3:ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)
  have hPcL : (P:L) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hA : A ≠ 0 := fun h => hPA (h ▸ dvd_zero _)
  have hE : E ≠ 0 := by
    intro h
    apply hPE
    change P ∣ E
    rw [h]
    exact dvd_zero _
  have hnL : (A:L)^2-(A:L)*(D:L)+(D:L)^2=(P:L)^2 := by exact_mod_cast hn
  have hy := GoldenCubicThueRootChange.depressed_root (A:L) (D:L) (P:L) x hnL hx
  have hθeq : θ^3-6*(P:L)*θ^2+9*(P:L)^2*θ-(E:L)^2*(P:L)=0 := by
    simpa [θ, α, E] using GoldenCubicThueRootChange.monic_root (P:L)
      ((A:L)-2*(D:L)) ((A:L)*x-(D:L)) hPcL hy
  have hθsq : θ^2=3*(P:L)*θ-(E:L)*(α-(D:L)) := by
    simpa [θ, α, E] using companion_square (P:L)
      ((A:L)-2*(D:L)) ((A:L)*x-(D:L)) hPcL hy
  let f := (GoldenCubicThueEisenstein.generator P E).toPoly
  have hmon : f.Monic := Cubic.monic_of_a_eq_one rfl
  have hdeg : f.natDegree = 3 := Cubic.natDegree_of_a_ne_zero (by change (1:ℤ) ≠ 0; decide)
  have hfroot : Polynomial.aeval θ f = 0 := by
    simp only [f, GoldenCubicThueEisenstein.generator, Cubic.toPoly,
      map_add, map_mul, map_pow, Polynomial.aeval_X, eq_intCast, map_intCast,
      map_neg, map_ofNat, Int.cast_one, one_mul]
    linear_combination hθeq
  have hθint : IsIntegral ℤ θ := ⟨f,hmon,hfroot⟩
  have hBC : (A:L)*x^3+(B:L)*x^2+(C:L)*x+(A:L)=0 := by
    dsimp [B,C]
    push_cast
    linear_combination hx
  have hint := scaled_basis_integral (L:=L) A B C x hBC
  have hαint : IsIntegral ℤ α := hint.1
  have hβint : IsIntegral ℤ β := by
    convert hint.2 using 1
    dsimp [β,B]
    push_cast
    ring
  have hθgen : IntermediateField.adjoin ℚ ({θ} : Set L) = ⊤ := by
    have hnQ : (A:ℚ)^2-(A:ℚ)*(D:ℚ)+(D:ℚ)^2=(P:ℚ)^2 := by exact_mod_cast hn
    have hAQ : (A:ℚ) ≠ 0 := by exact_mod_cast hA
    have hEQ : (A:ℚ)-2*(D:ℚ) ≠ 0 := by exact_mod_cast hE
    have hPQ : (P:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hxx : let a := algebraMap ℚ L (A:ℚ)
               let d := algebraMap ℚ L (D:ℚ)
               a*x^3-3*d*x^2+3*(d-a)*x+a=0 := by simpa only [map_intCast] using hx
    have h := GoldenCubicThueRootChange.same_simple_field
      (A:ℚ) (D:ℚ) (P:ℚ) x hAQ hPQ hEQ hnQ hxx
    simpa only [θ, α, map_intCast, hxgen] using h
  have hMk (i : Fin 4) : (![1,α,β,θ] : Fin 4 → L) i ∈ M :=
    Submodule.subset_span ⟨i,rfl⟩
  have h1M : 1 ∈ M := hMk 0
  have hαM : α ∈ M := hMk 1
  have hβM : β ∈ M := hMk 2
  have hθM : θ ∈ M := hMk 3
  have hθsqM : θ^2 ∈ M := by
    have hh : θ^2 = (3*P:ℤ) • θ - E • α + (E*D:ℤ) • (1:L) := by
      simp only [Algebra.smul_def, eq_intCast, Int.cast_mul, Int.cast_ofNat, mul_one]
      linear_combination hθsq
    rw [hh]
    exact M.add_mem (M.sub_mem (M.smul_mem _ hθM) (M.smul_mem _ hαM)) (M.smul_mem _ h1M)
  have hθ3 : θ^3 = ((6*P:ℤ):L)*θ^2+((-9*P^2:ℤ):L)*θ+((E^2*P:ℤ):L) := by
    push_cast
    linear_combination hθeq
  have hAdjoin : (adjoin ℤ ({θ} : Set L)).toSubmodule ≤ M :=
    adjoin_le_of_monic_cubic θ (6*P) (-9*P^2) (E^2*P) hθ3 M h1M hθM hθsqM
  have hBspan : Submodule.span ℤ (Set.range b) ≤ M := by
    rw [Submodule.span_le]
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · change b (0:Fin 3) ∈ M
      rw [hb0]
      exact h1M
    · change b (1:Fin 3) ∈ M
      rw [hb1]
      exact hαM
    · change b (2:Fin 3) ∈ M
      rw [hb2]
      exact hβM
  have hBint : ∀ i, IsIntegral ℤ (b i) := by
    intro i
    fin_cases i
    · change IsIntegral ℤ (b (0:Fin 3))
      rw [hb0]
      exact (isIntegral_one : IsIntegral ℤ (1:L))
    · change IsIntegral ℤ (b (1:Fin 3))
      rw [hb1]
      exact hαint
    · change IsIntegral ℤ (b (2:Fin 3))
      rw [hb2]
      exact hβint
  have htable := scaled_basis_products (A:L) (B:L) (C:L) x hBC
  have hβ' : (A:L)*x^2+(B:L)*x = β := by dsimp [B,β]; push_cast; ring
  dsimp only at htable
  rw [hβ'] at htable
  have haa : α*α = (A:ℚ) • β - (B:ℚ) • α := by
    simpa only [Algebra.smul_def, map_intCast, pow_two] using htable.1
  have hab : α*β = (-(C:ℚ)) • α - algebraMap ℚ L ((A:ℚ)^2) := by
    simpa only [Algebra.smul_def, map_intCast, map_neg, map_pow] using htable.2.1
  have hbb : β*β = (-(C:ℚ)) • β - (A:ℚ) • α - algebraMap ℚ L ((B:ℚ)*(A:ℚ)) := by
    simpa only [Algebra.smul_def, map_intCast, map_neg, map_mul, pow_two] using htable.2.2
  have hnQ : (A:ℚ)^2-(A:ℚ)*(D:ℚ)+(D:ℚ)^2=(P:ℚ)^2 := by exact_mod_cast hn
  have hcQ : (C:ℚ)=3*((D:ℚ)-(A:ℚ)) := by dsimp [C]; push_cast; ring
  have hbQ : (B:ℚ)=(-3)*(D:ℚ) := by dsimp [B]; push_cast; ring
  rw [hcQ] at hab hbb
  rw [hbQ] at haa hbb
  have htrace := traceMatrix_det_scaled_native b (A:ℚ) (D:ℚ) (P:ℚ) α β hb0 hb1 hb2 haa hab hbb hnQ
  have hdisc : Algebra.discr ℚ b = ((P^4 * (3:ℤ)^4 : ℤ):ℚ) := by
    rw [Algebra.discr_def, htrace]
    push_cast
    ring
  have hcop3A : ¬ (3:ℤ) ∣ A := by
    rintro ⟨k,hk⟩
    obtain ⟨l,hl⟩ := h3A
    omega
  have hcop : IsCoprime (A*E) (P^4 * (3:ℤ)^4) := by
    have hpAE : ¬ P ∣ A*E := fun h => (hp.dvd_or_dvd h).elim hPA hPE
    have h3AE : ¬ (3:ℤ) ∣ A*E := fun h => (hmod3.dvd_or_dvd h).elim hcop3A h3E
    exact ((hp.coprime_iff_not_dvd.mpr hpAE).symm.pow_right).mul_right
      ((hmod3.coprime_iff_not_dvd.mpr h3AE).symm.pow_right)
  have hclear : ∀ w ∈ M, (A*E) • w ∈ adjoin ℤ ({θ} : Set L) := by
    have hαrel : (E:L)*α = 3*(P:L)*θ - θ^2 + (E:L)*(D:L) := by linear_combination hθsq
    have hβrel : (A:L)*β = (P:L)*θ - (D:L)*α - (D:L)^2 := by
      have ht : (P:L)*θ=(α-(D:L))^2 := by
        dsimp [θ]; field_simp
      have hnume : (α-(D:L))^2 = (A:L)*β+(D:L)*α+(D:L)^2 :=
        companion_numerator (A:L) (D:L) x
      linear_combination -ht-hnume
    exact clear_span_enlarged A D E P α β θ hβrel hαrel
  have heiP : f.IsEisensteinAt (Ideal.span {P}) :=
    (GoldenCubicThueEisenstein.eisenstein_at_role P E hp.ne_zero
      (fun h => hPE (hp.dvd_of_dvd_pow h))).isEisensteinAt hp.not_isUnit
  have hei3 : (f.comp (X+Polynomial.C 1)).IsEisensteinAt (Ideal.span {(3:ℤ)}) :=
    GoldenCubicThueEisenstein.isEisensteinAt_three A D P hn h3A h3P
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w ⟨i,rfl⟩
    fin_cases i
    · exact isIntegral_one
    · exact hαint
    · exact hβint
    · exact hθint
  · intro z hz
    apply integral_span_of_eisenstein_translate b hBint θ hθgen
      hmon (by omega) hfroot hp hmod3 heiP hei3 M hAdjoin hBspan hcop hdisc hclear
    exact hz

/-- Saturating the native cubic order yields a one-denominator integral basis
and exact signed field discriminant, not just a polynomial discriminant. -/
theorem native_field_discriminant {L : Type*} [Field L] [NumberField L]
    (A D P : ℤ) (x : L) (hp : Prime P)
    (hPA : ¬ P ∣ A) (hPE : ¬ P ∣ A-2*D)
    (h3A : (3:ℤ) ∣ A-1) (h3E : ¬ (3:ℤ) ∣ A-2*D) (h3P : (3:ℤ) ∣ P-1)
    (hn : A^2-A*D+D^2=P^2)
    (hx : (A:L)*x^3-3*(D:L)*x^2+3*((D:L)-(A:L))*x+(A:L)=0)
    (hxgen : IntermediateField.adjoin ℚ ({x} : Set L) = ⊤)
    (b : Module.Basis (Fin 3) ℚ L) (hb0 : b 0 = 1)
    (hb1 : b 1 = (A:L)*x) (hb2 : b 2 = (A:L)*x^2-3*(D:L)*x) :
    NumberField.discr L = 81*P^2 ∧
    ∀ k l : ℤ, P ∣ A*k-D → P ∣ A*l-D^2 →
      let α := (A:L)*x
      let β := (A:L)*x^2-3*(D:L)*x
      let ω := (β+(k:L)*α+(l:L))/(P:L)
      Submodule.span ℤ (Set.range (![1,α,ω] : Fin 3 → L)) =
        (integralClosure ℤ L).toSubmodule := by
  let α := (A:L)*x
  let β := (A:L)*x^2-3*(D:L)*x
  let θ := (α-(D:L))^2/(P:L)
  have hmax := native_maximal_span A D P x hp hPA hPE h3A h3E h3P hn hx hxgen b hb0 hb1 hb2
  have hPcL : (P:L) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hPcQ : (P:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hPzero (z : L) (hz : (P:L)*z=0) : z=0 := (mul_eq_zero.mp hz).resolve_left hPcL
  obtain ⟨r,s,hBez⟩ := (hp.coprime_iff_not_dvd.mpr hPA).symm
  have hBezL : (r:L)*(A:L)+(s:L)*(P:L)=1 := by exact_mod_cast hBez
  have ht : (P:L)*θ = (α-(D:L))^2 := by dsimp [θ]; field_simp
  have hθnum : (P:L)*θ=(A:L)*β+(D:L)*α+(D:L)^2 := by
    exact ht.trans (companion_numerator (A:L) (D:L) x)
  have half (k l : ℤ) (hk : P ∣ A*k-D) (hl : P ∣ A*l-D^2) :
      Submodule.span ℤ (Set.range (![1,α,(β+(k:L)*α+(l:L))/(P:L)] : Fin 3 → L)) =
        (integralClosure ℤ L).toSubmodule := by
    obtain ⟨m,hm⟩ := hk
    obtain ⟨n,hn'⟩ := hl
    let ω := (β+(k:L)*α+(l:L))/(P:L)
    have hNum : (P:L)*ω=β+(k:L)*α+(l:L) := by dsimp [ω]; field_simp
    have hKm : A*k = D+P*m := by linear_combination hm
    have hLn : A*l = D^2+P*n := by linear_combination hn'
    have hKmL : (A:L)*(k:L)=(D:L)+(P:L)*(m:L) := by exact_mod_cast hKm
    have hLnL : (A:L)*(l:L)=(D:L)^2+(P:L)*(n:L) := by exact_mod_cast hLn
    obtain ⟨hθω,hωθ⟩ := enlarged_lattice_generators (A:L) (D:L) (P:L)
      α β θ ω (k:L) (l:L) (m:L) (n:L) (r:L) (s:L)
      hPzero hθnum hNum hKmL hLnL hBezL
    have hβrel : β=(P:L)*ω-(k:L)*α-(l:L) := by linear_combination -hNum
    have hωrel : ω=(r:L)*θ+((r*m+s*k:ℤ):L)*α+(s:L)*β+((r*n+s*l:ℤ):L) := by
      push_cast
      exact hωθ
    exact (enlarged_spans_eq α β θ ω A m n r (r*m+s*k) s (r*n+s*l)
      P k l hθω hωrel hβrel).symm.trans hmax
  refine ⟨?_, half⟩
  let k := r*D
  let l := r*D^2
  let ω := (β+(k:L)*α+(l:L))/(P:L)
  have hk : P ∣ A*k-D := ⟨-s*D, by dsimp [k]; linear_combination D*hBez⟩
  have hl : P ∣ A*l-D^2 := ⟨-s*D^2, by dsimp [l]; linear_combination D^2*hBez⟩
  have hmax' := half k l hk hl
  obtain ⟨b',hb'0,hb'1,hb'2⟩ := triangular_basis b (1:ℚ)
    ((l:ℚ)/(P:ℚ)) ((k:ℚ)/(P:ℚ)) ((P:ℚ)⁻¹) one_ne_zero (inv_ne_zero hPcQ)
  have hB' : ⇑b' = (![1,α,ω] : Fin 3 → L) := by
    funext i
    fin_cases i
    · change b' 0 = 1
      rw [hb'0,hb0]
    · change b' 1 = α
      rw [hb'1,hb1,one_smul]
    · change b' 2 = ω
      rw [hb'2,hb0,hb1,hb2]
      change (↑l / ↑P : ℚ) • (1:L) + (↑k / ↑P : ℚ) • α +
        ((↑P : ℚ)⁻¹) • β = ω
      simp only [ω, Algebra.smul_def, map_div₀, map_inv₀, map_intCast, mul_one]
      ring
  have hli : LinearIndependent ℚ (![1,α,ω] : Fin 3 → L) := by
    rw [← hB']
    exact b'.linearIndependent
  have hd := discr_eq_of_span_eq_integralClosure
    (![1,α,ω] : Fin 3 → L) hli hmax'
  have hB : ⇑b = (![1,α,β] : Fin 3 → L) := by
    funext i
    fin_cases i
    · exact hb0
    · exact hb1
    · exact hb2
  have hωq : ω = ((P:ℚ)⁻¹) • (β+(k:ℚ) • α+algebraMap ℚ L (l:ℚ)) := by
    simp only [ω, Algebra.smul_def, map_inv₀, map_intCast]
    ring
  have hdet :=
    trace_det_single_denominator α β (P:ℚ) (k:ℚ) (l:ℚ)
  rw [← hωq, ← hB] at hdet
  have hdisc : (traceMatrix ℚ b).det = 81*(P:ℚ)^4 := by
    have hnQ : (A:ℚ)^2-(A:ℚ)*(D:ℚ)+(D:ℚ)^2=(P:ℚ)^2 := by exact_mod_cast hn
    have htable := scaled_basis_products (A:L) (-3*(D:L)) (3*((D:L)-(A:L))) x (by
      linear_combination hx)
    have htable' : α^2=(A:L)*β-(-3*(D:L))*α ∧
        α*β=-(3*((D:L)-(A:L)))*α-(A:L)^2 ∧
        β^2=-(3*((D:L)-(A:L)))*β-(A:L)*α-(-3*(D:L))*(A:L) := by
      have hb' : (A:L)*x^2 + (-3*(D:L))*x = β := by dsimp [β]; ring
      dsimp only at htable
      rw [hb'] at htable
      exact htable
    refine traceMatrix_det_scaled_native b (A:ℚ) (D:ℚ) (P:ℚ) α β hb0 hb1 hb2 ?_ ?_ ?_ hnQ
    · simpa only [Algebra.smul_def,map_intCast,map_mul,map_neg,map_ofNat,pow_two] using htable'.1
    · simpa only [Algebra.smul_def,map_intCast,map_mul,map_sub,map_neg,map_ofNat,map_pow] using htable'.2.1
    · simpa only [Algebra.smul_def,map_intCast,map_mul,map_sub,map_neg,map_ofNat,pow_two] using htable'.2.2
  rw [Algebra.discr_def, hdet, hdisc] at hd
  have hdQ : (NumberField.discr L : ℚ) = 81*(P:ℚ)^2 := by
    rw [← hd]
    field_simp
  exact_mod_cast hdQ

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueMaximalOrder


set_option autoImplicit false
namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueMaximalOrder
open scoped IntermediateField

/-- A generating coordinate in a cubic fraction field gives its marked
power basis, with the three vectors in the intended order. -/
theorem cubic_power_basis {L : Type*} [Field L] [Algebra ℚ L] (x : L)
    (hx : IsIntegral ℚ x) (hgen : ℚ⟮x⟯ = ⊤) (h3 : Module.finrank ℚ L = 3) :
    ∃ b : Module.Basis (Fin 3) ℚ L, b 0=1 ∧ b 1=x ∧ b 2=x^2 := by
  let p := PowerBasis.ofAdjoinSimpleEqTop hx hgen
  have hp : p.gen = x := PowerBasis.ofAdjoinSimpleEqTop_gen hx hgen
  have hd : p.dim = 3 := p.finrank.symm.trans h3
  let b := p.basis.reindex (finCongr hd)
  have hb (i : Fin 3) : b i = x ^ (i:ℕ) := by
    rw [show b = p.basis.reindex (finCongr hd) by rfl, Module.Basis.reindex_apply]
    rw [p.basis_eq_pow, hp, finCongr_symm_apply_coe]
  exact ⟨b, by simpa using hb 0, by simpa using hb 1, by simpa using hb 2⟩

/-- Construct the actual old scaled basis from the original root, without
introducing an unspecified change of field or basis. -/
theorem native_scaled_basis {L : Type*} [Field L] [Algebra ℚ L] (A D : ℚ) (x : L)
    (hA : A ≠ 0) (hx : IsIntegral ℚ x) (hgen : ℚ⟮x⟯ = ⊤)
    (h3 : Module.finrank ℚ L = 3) :
    ∃ b : Module.Basis (Fin 3) ℚ L, b 0=1 ∧ b 1=A • x ∧
      b 2=A • x^2-3*algebraMap ℚ L D*x := by
  obtain ⟨b,h0,h1,h2⟩ := cubic_power_basis x hx hgen h3
  obtain ⟨u,hu0,hu1,hu2⟩ := triangular_basis b A 0 (-3*D) A hA hA
  refine ⟨u, hu0.trans h0, hu1.trans (by rw [h1]), ?_⟩
  rw [hu2,h0,h1,h2]
  simp only [Algebra.smul_def, map_mul, map_neg, map_ofNat, map_zero]
  ring

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueMaximalOrder

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueMaximalOrder
open Polynomial Algebra
open D5.S1.Scale
open D5.S3.Factorization.QuadraticIdeals
open EisensteinOddQuotient GoldenCubicThueDescent GoldenCubicThueEisenstein

/-- A cubic irreducible polynomial whose splitting field has dimension
three admits a marked root generating that actual splitting field. -/
theorem split_cubic_root (f : ℚ[X]) (hirr : Irreducible f)
    (hd : f.natDegree = 3) (hk : Module.finrank ℚ f.SplittingField = 3) :
    ∃ x : f.SplittingField, aeval x f = 0 ∧
      IntermediateField.adjoin ℚ ({x} : Set f.SplittingField) = ⊤ := by
  let L := f.SplittingField
  have hmapped : (f.map (algebraMap ℚ L)).natDegree = 3 := by
    rwa [natDegree_map_eq_of_injective (algebraMap ℚ L).injective]
  obtain ⟨x,hx⟩ := (Polynomial.SplittingField.splits f).exists_eval_eq_zero
    (degree_ne_of_natDegree_ne (by rw [hmapped]; decide : (f.map (algebraMap ℚ L)).natDegree ≠ 0))
  have hroot : aeval x f = 0 := by simpa only [eval_map, aeval_def] using hx
  refine ⟨x,hroot,?_⟩
  let K := IntermediateField.adjoin ℚ ({x} : Set L)
  have hm := minpoly.eq_of_irreducible hirr hroot
  have hlc : f.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hirr.ne_zero)
  have hdegree : (minpoly ℚ x).natDegree = 3 := by
    rw [← hm, natDegree_mul_C (p:=f) hlc, hd]
  have hk3 : Module.finrank ℚ K = 3 := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x), hdegree]
  have hdim := Module.finrank_mul_finrank ℚ K L
  rw [hk3, hk] at hdim
  have hKL : Module.finrank K L = 1 := by omega
  exact (IntermediateField.finrank_eq_one_iff_eq_top (K:=K)).mp hKL

/-- Bind the marked cubic field to the square role of the original
two-prime Lucas block, keeping the original oriented ideal witness. -/
theorem actual_factorization_marked_thue_field
    (j P Q : ℕ) (hj : 1 ≤ j) (hP : P.Prime) (hQ : Q.Prime) (hPQ : P ≠ Q)
    (hfact : blockNorm ((goldenLucas (3^j)-1).toNat) = P^2 * Q^3) :
    ∃ pi : EisensteinOrder,
      Ideal.span {pi} = orientedIdeal ((goldenLucas (3^j)-1).toNat) ⊔
        Ideal.span {(P:EisensteinOrder)} ∧
      QuadraticAlgebra.norm pi = (P:ℤ) ∧
      (3:EisensteinOrder) ∣ pi-1 ∧
      let A := pi.re^2-pi.im^2
      let D := 2*pi.re*pi.im-pi.im^2
      let f := (⟨(A:ℚ),(-3*D:ℤ),(3*(D-A):ℤ),(A:ℚ)⟩ : Cubic ℚ).toPoly
      let L := f.SplittingField
      Prime (P:ℤ) ∧ ¬ (P:ℤ) ∣ A ∧ ¬ (P:ℤ) ∣ A-2*D ∧
      (3:ℤ) ∣ A-1 ∧ ¬ (3:ℤ) ∣ A-2*D ∧ (3:ℤ) ∣ (P:ℤ)-1 ∧
      A^2-A*D+D^2=(P:ℤ)^2 ∧ Irreducible f ∧ Module.finrank ℚ L=3 ∧
      ∃ (x : L) (b : Module.Basis (Fin 3) ℚ L),
        (A:L)*x^3-3*(D:L)*x^2+3*((D:L)-(A:L))*x+(A:L)=0 ∧
        IntermediateField.adjoin ℚ ({x} : Set L)=⊤ ∧
        b 0=1 ∧ b 1=(A:L)*x ∧ b 2=(A:L)*x^2-3*(D:L)*x := by
  obtain ⟨pi, gamma, hnorm, _, _, _, hi, _, hp, _, _, _, _, hpacket⟩ :=
    (golden_cubic_exact_thue_descent j P Q hj hP hQ hPQ).1 hfact
  let a := pi.re
  let b := pi.im
  let A := a^2-b^2
  let D := 2*a*b-b^2
  let f := (⟨(A:ℚ),(-3*D:ℤ),(3*(D-A):ℤ),(A:ℚ)⟩ : Cubic ℚ).toPoly
  let L := f.SplittingField
  have hpn : a^2-a*b+b^2=(P:ℤ) := by
    have hh := hnorm
    simp only [QuadraticAlgebra.norm_def] at hh
    dsimp [a,b]
    linear_combination hh
  have hnp : Prime (P:ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hP)
  obtain ⟨ha,hb⟩ := primary_coordinate_divisibilities pi hp
  have hA3 : (3:ℤ) ∣ A-1 := by
    obtain ⟨k,hk⟩ := ha
    obtain ⟨l,hl⟩ := hb
    change a-1=3*k at hk
    change b=3*l at hl
    refine ⟨k*(a+1)-l*b,?_⟩
    dsimp [A]
    linear_combination (a+1)*hk-b*hl
  have hD3 : (3:ℤ) ∣ D := by
    obtain ⟨l,hl⟩ := hb
    change b=3*l at hl
    refine ⟨l*(2*a-b),?_⟩
    dsimp [D]
    linear_combination (2*a-b)*hl
  have hP3 : (3:ℤ) ∣ (P:ℤ)-1 := by
    obtain ⟨k,hk⟩ := ha
    obtain ⟨l,hl⟩ := hb
    change a-1=3*k at hk
    change b=3*l at hl
    refine ⟨k*(a+1)+l*(b-a),?_⟩
    linear_combination -hpn+(a+1)*hk+(b-a)*hl
  have hPnd : ¬ (P:ℤ) ∣ (3:ℤ) := by
    obtain ⟨k,hk⟩ := hP3
    rintro ⟨l,hl⟩
    apply hnp.not_isUnit
    apply isUnit_of_dvd_one
    refine ⟨1-l*k,?_⟩
    linear_combination -hk-k*hl
  have hE3 : ¬ (3:ℤ) ∣ A-2*D := by
    obtain ⟨k,hk⟩ := hA3
    obtain ⟨l,hl⟩ := hD3
    rintro ⟨m,hm⟩
    omega
  obtain ⟨hAn,hEn⟩ := not_dvd_generator_discriminant_factors hnp hPnd hpn
  have hn : A^2-A*D+D^2=(P:ℤ)^2 := by
    dsimp [A,D]
    rw [primary_norm_identity, hpn]
  have hA : A ≠ 0 := by
    change ¬ (P:ℤ) ∣ A at hAn
    exact fun he => hAn (he ▸ dvd_zero _)
  have haQ : (A:ℚ) ≠ 0 := by exact_mod_cast hA
  have hfd : f.natDegree=3 := Cubic.natDegree_of_a_ne_zero haQ
  -- The irreducible polynomial and the dimension are from the very same pair.
  have hirr : Irreducible f := hpacket.2.2.2.1.1
  have hdim : Module.finrank ℚ L=3 := hpacket.2.2.2.1.2.1
  obtain ⟨x,hx,hxgen⟩ := split_cubic_root f hirr hfd hdim
  have hxform : (A:L)*x^3-3*(D:L)*x^2+3*((D:L)-(A:L))*x+(A:L)=0 := by
    have hrootL : f.eval₂ (algebraMap ℚ L) (x:L) = 0 := hx
    simp only [f,Cubic.toPoly,Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_pow,
      Polynomial.eval₂_C,Polynomial.eval₂_X,map_intCast, Int.cast_mul, Int.cast_neg, Int.cast_ofNat,
      Int.cast_sub] at hrootL
    have evalInt (n : ℤ) :
        ((n:ℚ[X]).eval₂ (algebraMap ℚ L) (x:L)) = (n:L) :=
      map_intCast (Polynomial.eval₂RingHom (algebraMap ℚ L) (x:L)) n
    simp only [evalInt,map_mul,map_sub,map_neg,map_ofNat,map_intCast] at hrootL
    linear_combination hrootL
  obtain ⟨v,hv0,hv1,hv2⟩ := native_scaled_basis (A:ℚ) (D:ℚ) x
    haQ (Algebra.IsIntegral.isIntegral x) hxgen hdim
  refine ⟨pi,hi,hnorm,hp,hnp,hAn,hEn,hA3,hE3,hP3,hn,hirr,hdim,x,v,hxform,hxgen,hv0,?_,?_⟩
  · simpa only [Algebra.smul_def,map_intCast] using hv1
  · simpa only [Algebra.smul_def,map_intCast] using hv2


open D5.S1.Scale
open EisensteinOddQuotient GoldenCubicThueDescent GoldenCubicThueEisenstein

local instance splittingFieldNumberField (f : ℚ[X]) : NumberField f.SplittingField :=
  NumberField.of_module_finite ℚ f.SplittingField

/-- The original two-prime factorization forces the actual marked Thue
splitting field to have signed discriminant 81P² and the displayed
one-denominator integral basis. No generator shape is an extra hypothesis. -/
theorem actual_factorization_field_discriminant
    (j P Q : ℕ) (hj : 1 ≤ j) (hP : P.Prime) (hQ : Q.Prime) (hPQ : P ≠ Q)
    (hfact : blockNorm ((goldenLucas (3^j)-1).toNat) = P^2 * Q^3) :
    ∃ pi : EisensteinOrder,
      Ideal.span {pi} = orientedIdeal ((goldenLucas (3^j)-1).toNat) ⊔
        Ideal.span {(P:EisensteinOrder)} ∧
      QuadraticAlgebra.norm pi = (P:ℤ) ∧
      (3:EisensteinOrder) ∣ pi-1 ∧
      let A := pi.re^2-pi.im^2
      let D := 2*pi.re*pi.im-pi.im^2
      let f := (⟨(A:ℚ),(-3*D:ℤ),(3*(D-A):ℤ),(A:ℚ)⟩ : Cubic ℚ).toPoly
      let L := f.SplittingField
      NumberField.discr L = 81*(P:ℤ)^2 ∧
      ∃ x : L,
        (A:L)*x^3-3*(D:L)*x^2+3*((D:L)-(A:L))*x+(A:L)=0 ∧
        IntermediateField.adjoin ℚ ({x} : Set L)=⊤ ∧
        ∃ k l : ℤ,
          (P:ℤ) ∣ A*k-D ∧ (P:ℤ) ∣ A*l-D^2 ∧
          let α := (A:L)*x
          let β := (A:L)*x^2-3*(D:L)*x
          let ω := (β+(k:L)*α+(l:L))/(P:L)
          Submodule.span ℤ (Set.range (![1,α,ω] : Fin 3 → L)) =
            (integralClosure ℤ L).toSubmodule := by
  classical
  obtain ⟨pi,hi,hnorm,hprim,hp,hPA,hPE,h3A,h3E,h3P,hn,_,_,x,b,hx,hgen,hb0,hb1,hb2⟩ :=
    actual_factorization_marked_thue_field j P Q hj hP hQ hPQ hfact
  let A := pi.re^2-pi.im^2
  let D := 2*pi.re*pi.im-pi.im^2
  have hPA' : ¬ (P:ℤ) ∣ A := hPA
  have hd := native_field_discriminant A D (P:ℤ) x hp hPA' hPE h3A h3E h3P hn hx hgen
    b hb0 hb1 hb2
  obtain ⟨r,s,hrs⟩ := (hp.coprime_iff_not_dvd.mpr hPA').symm
  let k := r*D
  let l := r*D^2
  have hk : (P:ℤ) ∣ A*k-D := ⟨-s*D, by dsimp [k]; linear_combination D*hrs⟩
  have hl : (P:ℤ) ∣ A*l-D^2 := ⟨-s*D^2, by dsimp [l]; linear_combination D^2*hrs⟩
  exact ⟨pi,hi,hnorm,hprim,hd.1,x,hx,hgen,k,l,hk,hl,hd.2 k l hk hl⟩

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueMaximalOrder
